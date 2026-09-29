-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/15697556-3ab0-59db-9e9c-cd888f9700e0

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace K2Nilp

open MvPowerSeries

variable {B : Type} [CommRing B]

def Tgt (_φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) : Type := MvPowerSeries (Fin 2) B

noncomputable scoped instance (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) : CommRing (Tgt φ) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin 2) B))

def toTgt (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) : MvPowerSeries (Fin 2) B →+* Tgt φ := φ

noncomputable scoped instance (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) :
    Algebra (MvPowerSeries (Fin 2) B) (Tgt φ) := (toTgt φ).toAlgebra

noncomputable def ofT (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) :
    Tgt φ ≃+* MvPowerSeries (Fin 2) B := RingEquiv.refl _

theorem ofT_algebraMap (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) (r : MvPowerSeries (Fin 2) B) :
    ofT φ (algebraMap (MvPowerSeries (Fin 2) B) (Tgt φ) r) = φ r := rfl

theorem ofT_smul (φ : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) (r : MvPowerSeries (Fin 2) B)
    (t : Tgt φ) : ofT φ (r • t) = φ r * ofT φ t := by
  rw [Algebra.smul_def, map_mul, ofT_algebraMap]

theorem mem_span_X_pow {σ : Type*} [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ B, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ B := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ B) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ B) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

theorem mem_span_range_X_of_constantCoeff {n : ℕ} {f : MvPowerSeries (Fin n) B}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) B)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

end K2Nilp
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp.K2Nilp"

open MvPowerSeries K2Nilp in
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] {φ ψ : Series B} {d : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ d)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range (ψ.comp φ))) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range ψ) := by
  classical
  obtain ⟨hfinK, -, -⟩ := hφ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0

  have hinj : ∀ f g : MvPowerSeries (Fin 2) B, subst φ f = subst φ g → f = g :=
    CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_residueFields φ hφ0 hfinK
      (fun κ _ g _ hfin' f' g' h =>
        CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_field (φ.map g)
          (fun i => by
            show constantCoeff (MvPowerSeries.map g (φ i)) = 0
            rw [constantCoeff_map, hφ0, map_zero])
          hfin' f' g' h)

  let φa : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B := substAlgHom (R := B) hφs
  let φr : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B := φa.toRingHom
  have hφr : ∀ f, φr f = subst φ f := fun f => by
    show φa f = _
    rw [coe_substAlgHom]
  let S := MvPowerSeries (Fin 2) B
  let T := Tgt φr
  let ε : T ≃+* MvPowerSeries (Fin 2) B := ofT φr
  have hε_smul : ∀ (r : S) (t : T), ε (r • t) = φr r * ε t := ofT_smul φr
  have hε_symm : ∀ x, ε (ε.symm x) = x := fun x => rfl

  haveI : Module.Finite B (FormalODModule.KerAlgebra φ) := hfinK
  obtain ⟨r, sgen, hsgen⟩ := Module.Finite.exists_fin (R := B) (M := FormalODModule.KerAlgebra φ)
  choose b hb using fun j => Ideal.Quotient.mk_surjective (sgen j)
  have hgen : Submodule.span B (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range φ)) (b j)) = ⊤ := by
    have : (fun j => Ideal.Quotient.mk (Ideal.span (Set.range φ)) (b j)) = sgen := funext hb
    rw [this]
    exact hsgen
  have hexp := MvPowerSeries.exists_eq_sum_subst_mul_of_span_quotient_eq_top φ hφ0 b hgen
  haveI hfinT : Module.Finite S T := by
    refine Module.Finite.of_surjective (Fintype.linearCombination S fun j => ε.symm (b j)) fun t => ?_
    obtain ⟨c, hc⟩ := hexp (ε t)
    refine ⟨c, ε.injective ?_⟩
    rw [Fintype.linearCombination_apply, map_sum, hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hε_smul, hε_symm, hφr]

  let I : Ideal S := Ideal.span (Set.range ψ)
  let J : Ideal (MvPowerSeries (Fin 2) B) := Ideal.span (Set.range (ψ.comp φ))
  have hIJ : ∀ y ∈ J, ε.symm y ∈ (I • ⊤ : Submodule S T) := by
    intro y hy
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have hle : Ideal.map (ε.symm : MvPowerSeries (Fin 2) B →+* T) J ≤ Ideal.map (algebraMap S T) I := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      have : (ε.symm : MvPowerSeries (Fin 2) B →+* T) ((ψ.comp φ) j) = algebraMap S T (ψ j) := by
        apply ε.injective
        show ε (ε.symm ((ψ.comp φ) j)) = ε (algebraMap S T (ψ j))
        rw [hε_symm, ofT_algebraMap, hφr]
        rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
    exact hle (Ideal.mem_map_of_mem _ hy)

  obtain ⟨N, hN⟩ := hN
  have hφnil : ∀ i, ∃ L : ℕ, φ i ^ L ∈ J := by
    intro i
    have hx : ∀ k : Fin 2, IsNilpotent (Ideal.Quotient.mk J (X k)) := fun k =>
      ⟨N, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hN k⟩
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries (Fin 2) B)).mp
      (mem_span_range_X_of_constantCoeff (hφ0 i))
    have hnil : IsNilpotent (Ideal.Quotient.mk J (φ i)) := by
      rw [← hq, map_sum]
      refine isNilpotent_sum (fun k _ => ?_)
      rw [smul_eq_mul, map_mul]
      exact (Commute.all _ _).isNilpotent_mul_left (hx k)
    obtain ⟨L, hL⟩ := hnil
    exact ⟨L, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hL⟩

  have key : ∀ i : Fin 2, ∃ e : ℕ, (X i : S) ^ e ∈ I := by
    intro i
    obtain ⟨L, hL⟩ := hφnil i
    let t : S := X i ^ L
    have hφt : φr t = φ i ^ L := by
      show φa (X i ^ L) = _
      rw [map_pow, substAlgHom_X]
    let f : Module.End S T := algebraMap S (Module.End S T) t
    have hrange : LinearMap.range f ≤ (I • ⊤ : Submodule S T) := by
      rintro _ ⟨m, rfl⟩
      have hmem : ε (f m) ∈ J := by
        have hfm : f m = t • m := by simp only [f, Module.algebraMap_end_apply]
        rw [hfm, hε_smul, hφt]
        exact J.mul_mem_right _ hL
      exact hIJ _ hmem
    obtain ⟨p, hmonic, -, hcoeff, haeval⟩ :=
      LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul S f I hrange

    have h1 : p.eval t = 0 := by
      have h := congrArg (fun g : Module.End S T => ε (g (ε.symm 1))) haeval
      simp only [f, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply,
        LinearMap.zero_apply, map_zero, hε_smul, hε_symm, mul_one] at h
      refine hinj _ _ ?_
      rw [← hφr, h, ← hφr, map_zero]

    have h2 : t ^ p.natDegree ∈ I := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_mul] at h1
      have : t ^ p.natDegree = -∑ k ∈ Finset.range p.natDegree, p.coeff k * t ^ k := by
        linear_combination h1
      rw [this]
      refine I.neg_mem (I.sum_mem fun k hk => I.mul_mem_right _ ?_)
      have hk' : p.natDegree - k ≠ 0 := by
        have := Finset.mem_range.mp hk
        omega
      exact Ideal.pow_le_self hk' (hcoeff k)
    exact ⟨L * p.natDegree, by rw [pow_mul]; exact h2⟩
  obtain ⟨e₀, he₀⟩ := key 0
  obtain ⟨e₁, he₁⟩ := key 1
  refine ⟨e₀ + e₁, fun i => ?_⟩
  fin_cases i
  · rw [pow_add]; exact I.mul_mem_right _ he₀
  · rw [pow_add]; exact I.mul_mem_left _ he₁

end S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp (solution)
