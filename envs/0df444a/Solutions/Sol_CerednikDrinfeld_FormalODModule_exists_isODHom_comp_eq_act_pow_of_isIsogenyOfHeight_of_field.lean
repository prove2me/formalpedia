-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/69d3af1c-6d16-5571-8a8d-b08783a542f1

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Theorems.Thm_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
import Theorems.Thm_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isODHom_of_comp_eq_act_pow_of_subst_injective
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace S3Asm

section NilEval
variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {C : Type} [CommRing C] [Algebra B C]

noncomputable abbrev bnd (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

theorem le_bnd_iff (n : ℕ) (m : σ →₀ ℕ) : m ≤ bnd σ n ↔ ∀ i, m i ≤ n := by
  simp [bnd, Finsupp.le_def]

theorem prod_pow_eq_zero (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (m : σ →₀ ℕ) (hm : ¬ m ≤ bnd σ n) : (m.prod fun i k => a i ^ k) = 0 := by
  rw [le_bnd_iff] at hm
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  rw [Finsupp.prod]
  have hi' : i ∈ m.support := by
    rw [Finsupp.mem_support_iff]; omega
  apply Finset.prod_eq_zero hi'
  have : a i ^ (n + 1) = 0 := by
    have := Ideal.pow_mem_pow (ha i) (n + 1)
    rwa [hJ, Ideal.mem_bot] at this
  rw [show m i = (n + 1) + (m i - (n + 1)) by omega, pow_add, this, zero_mul]

theorem aeval_eq_zero_of_coeff (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (P : MvPolynomial σ B) (hP : ∀ m, m ≤ bnd σ n → P.coeff m = 0) : MvPolynomial.aeval a P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m ≤ bnd σ n
  · rw [hP m hm, map_zero, zero_mul]
  · rw [← Finsupp.prod, prod_pow_eq_zero J n hJ a ha m hm, mul_zero]

theorem nilEval_def (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → C) :
    MvFormalGroup.nilEval n φ a = MvPolynomial.aeval a (trunc' B (bnd σ n) φ) := rfl

theorem nilEval_add (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ + ψ) a = MvFormalGroup.nilEval n φ a + MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_add]
  congr 1
  ext m
  simp only [coeff_trunc', MvPolynomial.coeff_add, map_add]

theorem nilEval_sub (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ - ψ) a = MvFormalGroup.nilEval n φ a - MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_sub]
  congr 1
  ext m
  simp only [coeff_trunc', MvPolynomial.coeff_sub, map_sub]

theorem nilEval_mul (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ * ψ) a = MvFormalGroup.nilEval n φ a * MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_mul, ← sub_eq_zero, ← map_sub]
  apply aeval_eq_zero_of_coeff J n hJ a ha
  intro m hm
  rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos hm, MvPolynomial.coeff_mul, coeff_mul, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro x hx
  have hx1 : x.1 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_self_add) hm
  have hx2 : x.2 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_add_self) hm
  rw [coeff_trunc', coeff_trunc', if_pos hx1, if_pos hx2]

theorem nilEval_C (n : ℕ) (a : σ → C) (b : B) :
    MvFormalGroup.nilEval n (MvPowerSeries.C b) a = algebraMap B C b := by
  rw [nilEval_def]
  have : trunc' B (bnd σ n) (MvPowerSeries.C b) = MvPolynomial.C b := by
    ext m
    rw [coeff_trunc', MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg (show ¬ (0 = m) from fun h => h0 h.symm)]
      all_goals (split_ifs <;> rfl)
  rw [this, MvPolynomial.aeval_C]

theorem nilEval_zero (n : ℕ) (a : σ → C) : MvFormalGroup.nilEval n (0 : MvPowerSeries σ B) a = 0 := by
  rw [show (0 : MvPowerSeries σ B) = MvPowerSeries.C 0 from (map_zero _).symm, nilEval_C, map_zero]

noncomputable def nilEvalRingHom (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvPowerSeries σ B →+* C where
  toFun φ := MvFormalGroup.nilEval n φ a
  map_one' := by rw [show (1 : MvPowerSeries σ B) = MvPowerSeries.C 1 from (map_one _).symm, nilEval_C, map_one]
  map_mul' φ ψ := nilEval_mul J n hJ a ha φ ψ
  map_zero' := nilEval_zero n a
  map_add' φ ψ := nilEval_add n a φ ψ

theorem nilEval_eq_zero_of_mem_span (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    {ι : Type} (f : ι → MvPowerSeries σ B) (hf : ∀ i, MvFormalGroup.nilEval n (f i) a = 0)
    {G : MvPowerSeries σ B} (hG : G ∈ Ideal.span (Set.range f)) : MvFormalGroup.nilEval n G a = 0 := by
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker (nilEvalRingHom J n hJ a ha : MvPowerSeries σ B →+* C) :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (RingHom.mem_ker).mpr (hf i))
  exact (RingHom.mem_ker).mp (hle hG)

end NilEval

end S3Asm

open S3Asm in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [Field B] (hB : IsNilpotent (p : B))
    (X Y : FormalODModule p B) (ρ : Series B) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight X Y ρ h) :
    ∃ (N : ℕ) (β : Series B), FormalODModule.IsODHom Y X β ∧ β.comp ρ = X.act ((p : Zp2 p) ^ N) := by
  classical
  obtain ⟨hhom, hker⟩ := hρ

  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem p hB X ρ
    (CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree ρ hhom.1.1 hker)
  have hN' : ∀ i, X.F.nthSeries (p ^ N) i ∈ Ideal.span (Set.range ρ) := fun i => by
    rw [← X.act_natCast, Nat.cast_pow]; exact hN i

  have hNx := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree ρ hhom.1.1 hker
  have hinj : ∀ H H' : MvPowerSeries (Fin 2) B, MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H' → H = H' :=
    fun H H' hh => CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree ρ hhom.1.1 hker H H' hh
  have hinj2 := fun H H' hh => MvPowerSeries.subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span ρ hhom.1.1 hNx hker.1 hker.2.1 H H' hh
  have hdesc := fun G hG => MvFormalGroup.exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_field X.F Y.F ρ hhom.1.1 hhom.1.2 hNx hker.1 hker.2.1 G hG

  have hinv : ∀ i : Fin 2,
      MvPowerSeries.subst X.F.toPowerSeries (X.F.nthSeries (p ^ N) i) -
          MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
            (X.F.nthSeries (p ^ N) i) ∈
        Ideal.span (Set.range fun j => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)) := by
    intro i
    apply MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
    intro C _ _ J m hJ s hs hS

    set sx : Fin 2 → C := fun l => s (Sum.inl l) with hsx
    set sz : Fin 2 → C := fun l => s (Sum.inr l) with hsz
    have hsx' : ∀ l, sx l ∈ J := fun l => hs _
    have hsz' : ∀ l, sz l ∈ J := fun l => hs _
    have hselim : Sum.elim sx sz = s := by funext t; rcases t with l | l <;> rfl
    have hXl : ∀ l : Fin 2, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 := fun l => MvPowerSeries.constantCoeff_X _
    have hXr : ∀ l : Fin 2, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 := fun l => MvPowerSeries.constantCoeff_X _
    have hevl : (fun l : Fin 2 => MvFormalGroup.nilEval m
        ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) s) = sx := by
      funext l; rw [MvFormalGroup.nilEval_X_of_mem J m hJ s hs]
    have hevr : (fun l : Fin 2 => MvFormalGroup.nilEval m
        ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) s) = sz := by
      funext l; rw [MvFormalGroup.nilEval_X_of_mem J m hJ s hs]

    have hρz : ∀ j, MvFormalGroup.nilEval m (ρ j) sz = 0 := by
      intro j
      have h := hS _ ⟨j, rfl⟩
      change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (ρ j)) s = 0 at h
      rwa [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXr (ρ j)).2, hevr] at h
    have hNz : ∀ j, MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sz = 0 := fun j =>
      nilEval_eq_zero_of_mem_span J m hJ sz hsz' ρ hρz (hN' j)

    rw [nilEval_sub, (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXl _).2, hevl,
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs X.F.toPowerSeries X.F.constantCoeff_eq_zero _).2]

    have hwJ : ∀ j, MvFormalGroup.nilEval m (X.F.toPowerSeries j) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs X.F.toPowerSeries X.F.constantCoeff_eq_zero 0).1
    have huJ : ∀ j, MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ sx hsx' (X.F.nthSeries (p ^ N))
        (MvFormalGroup.constantCoeff_nthSeries X.F _) 0).1

    have hlaw := (X.isLawHom_act ((p : Zp2 p) ^ N)).2 i
    rw [← Nat.cast_pow, X.act_natCast] at hlaw
    have key := congrArg (fun G => MvFormalGroup.nilEval m G s) hlaw
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs X.F.toPowerSeries X.F.constantCoeff_eq_zero _).2] at key
    have hfam0 : ∀ t, MvPowerSeries.constantCoeff (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (X.F.nthSeries (p ^ N) j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (X.F.nthSeries (p ^ N) j)) t) = 0 := by
      rintro (j | j)
      · exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hXl) hXl
          (MvFormalGroup.constantCoeff_nthSeries X.F _ j)
      · exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hXr) hXr
          (MvFormalGroup.constantCoeff_nthSeries X.F _ j)
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hfam0 _).2] at key
    have hinner : (fun t => MvFormalGroup.nilEval m (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (X.F.nthSeries (p ^ N) j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
          (X.F.nthSeries (p ^ N) j)) t) s) =
        Sum.elim (fun j => MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx) (fun _ => 0) := by
      funext t
      rcases t with j | j
      · change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (X.F.nthSeries (p ^ N) j)) s =
          MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx
        rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXl _).2, hevl]
      · change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (X.F.nthSeries (p ^ N) j)) s = 0
        rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXr _).2, hevr]
        exact hNz j
    rw [hinner] at key

    have hunit : MvFormalGroup.nilEval m (X.F.toPowerSeries i)
        (Sum.elim (fun j => MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx) (fun _ => 0)) =
        MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) i) sx := by
      have hfam1 : ∀ t : Fin 2 ⊕ Fin 2, MvPowerSeries.constantCoeff (Sum.elim (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin 2) B))
          (fun (_ : Fin 2) => (0 : MvPowerSeries (Fin 2) B)) t) = 0 := by
        rintro (j | j)
        · exact MvPowerSeries.constantCoeff_X _
        · exact map_zero _
      have h1 := (MvFormalGroup.nilEval_subst_of_mem J m hJ _ huJ _ hfam1 (X.F.toPowerSeries i)).2
      rw [X.F.subst_elim_X_zero i, MvFormalGroup.nilEval_X_of_mem J m hJ _ huJ i] at h1
      have hin2 : (fun t : Fin 2 ⊕ Fin 2 => MvFormalGroup.nilEval m (Sum.elim (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin 2) B))
          (fun (_ : Fin 2) => (0 : MvPowerSeries (Fin 2) B)) t) (fun j => MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx)) =
          Sum.elim (fun j => MvFormalGroup.nilEval m (X.F.nthSeries (p ^ N) j) sx) (fun _ => 0) := by
        funext t
        rcases t with j | j
        · exact MvFormalGroup.nilEval_X_of_mem J m hJ _ huJ j
        · exact nilEval_zero m _
      rw [hin2] at h1
      exact h1.symm
    rw [key, hunit, sub_self]

  choose β hβ using fun i => hdesc (X.F.nthSeries (p ^ N) i) (hinv i)
  have hβρ : Series.comp β ρ = X.act ((p : Zp2 p) ^ N) := by
    funext i
    rw [← Nat.cast_pow, X.act_natCast]
    exact (hβ i).1.symm
  have hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0 := fun i => by
    rw [(hβ i).2]; exact MvFormalGroup.constantCoeff_nthSeries X.F _ i
  exact ⟨N, β, CerednikDrinfeld.FormalODModule.isODHom_of_comp_eq_act_pow_of_subst_injective p X Y ρ β N hhom hinj hinj2 hβ0 hβρ, hβρ⟩

end S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field (solution)
