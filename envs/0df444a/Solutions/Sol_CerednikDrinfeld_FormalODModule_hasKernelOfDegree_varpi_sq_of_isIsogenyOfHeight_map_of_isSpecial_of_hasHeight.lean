-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ba3397c1-3fc5-5a0e-ba7f-6ab3b11afd64

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
import Theorems.Thm_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace W26

open MvPowerSeries

section Peel
variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem exists_eq_sum_X_mul_of_constantCoeff [Fintype σ] (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) : ∃ q : σ → MvPowerSeries σ R, f = ∑ s, X s * q s := by
  classical
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  exact ⟨q, hq⟩

theorem subst_mem_span [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul_of_constantCoeff f hf
  rw [hq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom hsa, subst_X hsa]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end Peel

theorem moduleFinite_quotient_of_X_pow_mem {R : Type} [CommRing R] {g : ℕ} (I : Ideal (MvPowerSeries (Fin g) R)) (N : ℕ)
    (hI : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N ∈ I) : Module.Finite R (MvPowerSeries (Fin g) R ⧸ I) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (MvPowerSeries (Fin g) R) := ⟨fun a b => MvPowerSeries.ext fun d => Subsingleton.elim _ _⟩
    haveI : Subsingleton (MvPowerSeries (Fin g) R ⧸ I) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact congrArg _ (Subsingleton.elim a b)
    infer_instance
  · let J : Ideal (MvPowerSeries (Fin g) R) := Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N)
    haveI : Module.Finite R (MvPowerSeries (Fin g) R ⧸ J) :=
      (MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow R g (fun _ => N)).2.1
    have hJI : J ≤ I := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hI i
    exact Module.Finite.of_surjective ((Ideal.Quotient.factorₐ R hJI).toLinearMap) (Ideal.Quotient.factor_surjective hJI)

variable {p : ℕ} [Fact p.Prime]

theorem exists_X_pow_mem_span_varpi {B : Type} [CommRing B] [IsNoetherianRing B] (Y : FormalODModule p B) (hY : Y.HasHeight 4) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range Y.varpi) := by
  have hact0 : ∀ i, MvPowerSeries.constantCoeff (Y.act (p : Zp2 p) i) = 0 := (Y.isLawHom_act _).1
  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (Y.act (p : Zp2 p)) hact0 hY
  have hle : Ideal.span (Set.range (Y.act (p : Zp2 p))) ≤ Ideal.span (Set.range Y.varpi) := by
    rw [← Y.varpi_comp_varpi, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact subst_mem_span Y.isLawHom_varpi.1 (Y.isLawHom_varpi.1 i)
  exact ⟨N, fun i => hle (hN i)⟩

theorem hasKernelOfDegree_varpi_of_hasHeight_four {B : Type} [CommRing B] [IsNoetherianRing B] (Y : FormalODModule p B)
    (hY : Y.HasHeight 4) : FormalODModule.HasKernelOfDegree Y.varpi (p ^ 2) := by
  have hv0 : ∀ i, MvPowerSeries.constantCoeff (Y.varpi i) = 0 := Y.isLawHom_varpi.1
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem Y.varpi hv0
    (exists_X_pow_mem_span_varpi Y hY)
  refine ⟨hfin, hproj, fun κ _ g => ?_⟩

  let Yκ : FormalODModule p κ := Y.map g
  have hYκ : Yκ.HasHeight 4 := by
    change FormalODModule.HasKernelOfDegree ((Y.map g).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map g _ ((Y.isLawHom_act _).1) hY
  have hvκ0 : ∀ i, MvPowerSeries.constantCoeff (Yκ.varpi i) = 0 := Yκ.isLawHom_varpi.1
  obtain ⟨N, hNκ⟩ := exists_X_pow_mem_span_varpi Yκ hYκ
  haveI hfinκ : Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range Yκ.varpi)) :=
    moduleFinite_quotient_of_X_pow_mem _ N hNκ

  obtain ⟨-, hmul⟩ := MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul Yκ.varpi Yκ.varpi hvκ0 hvκ0 hfinκ hfinκ
  have hcomp : (fun i => MvPowerSeries.subst Yκ.varpi (Yκ.varpi i)) = Yκ.act (p : Zp2 p) := Yκ.varpi_comp_varpi
  rw [hcomp] at hmul
  have h4 : Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (Yκ.act (p : Zp2 p)))) = p ^ 4 := by
    have := hYκ.2.2 κ (RingHom.id κ)
    rwa [show (Yκ.act (p : Zp2 p)).map (RingHom.id κ) = Yκ.act (p : Zp2 p) from
      funext fun i => by simp [Series.map, MvPowerSeries.map_id]] at this
  rw [h4, show p ^ 4 = p ^ 2 * p ^ 2 by ring] at hmul
  have ha : Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range Yκ.varpi)) = p ^ 2 :=
    Nat.mul_self_inj.1 hmul.symm

  have hmap : Yκ.varpi = Y.varpi.map g := FormalODModule.map_varpi g Y
  rw [hmap] at ha
  exact ha

end W26

theorem solution
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] (j₀ : Zp2 p →+* k)
    (Φ : FormalODModule p k) (hΦs : Φ.IsSpecial j₀) (hΦ4 : Φ.HasHeight 4)
    {L : Type} [CommRing L] [IsNoetherianRing L] (hLp : IsNilpotent ((p : ℕ) : L))
    (f : k →+* L ⧸ pIdeal p L) (X : FormalODModule p L) (ρ : Series (L ⧸ pIdeal p L)) (h : ℕ)
    (hρ : FormalODModule.IsIsogenyOfHeight (Φ.map f) (X.map (Ideal.Quotient.mk (pIdeal p L))) ρ h) :
    FormalODModule.HasKernelOfDegree X.varpi (p ^ 2) := by
  let B := L ⧸ pIdeal p L
  have hv0 : ∀ i, MvPowerSeries.constantCoeff (X.varpi i) = 0 := X.isLawHom_varpi.1

  have hΦf : (Φ.map f).HasHeight 4 := by
    change FormalODModule.HasKernelOfDegree ((Φ.map f).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f _ ((Φ.isLawHom_act _).1) hΦ4
  have hB : IsNilpotent ((p : ℕ) : B) := by
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hXbar : (X.map (Ideal.Quotient.mk (pIdeal p L))).HasHeight 4 :=
    CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight p hB _ _ ρ h hρ hΦf
  have hbar := W26.hasKernelOfDegree_varpi_of_hasHeight_four _ hXbar
  rw [FormalODModule.map_varpi] at hbar

  refine CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
    (Ideal.Quotient.mk (pIdeal p L)) Ideal.Quotient.mk_surjective ?_ X.varpi hv0 (pow_pos (Fact.out : p.Prime).pos 2) hbar
  rw [Ideal.mk_ker]
  obtain ⟨n, hn⟩ := hLp
  refine ⟨n, ?_⟩
  rw [show pIdeal p L = Ideal.span {((p : ℕ) : L)} from rfl, Ideal.span_singleton_pow, hn, Ideal.span_singleton_eq_bot.2 rfl]
  rfl

end S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_varpi_sq_of_isIsogenyOfHeight_map_of_isSpecial_of_hasHeight (solution)
