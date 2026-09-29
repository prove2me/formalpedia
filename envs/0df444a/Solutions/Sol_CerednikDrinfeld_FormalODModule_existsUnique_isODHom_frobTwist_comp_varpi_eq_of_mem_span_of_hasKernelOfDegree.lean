-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.existsUnique_isODHom_frobTwist_comp_varpi_eq_of_mem_span_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6ee825dc-09dd-5d7d-b58c-4bb072208951

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ODModuleFrobeniusTwist
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_MvFormalGroup_subst_injective_and_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_isODHom_frobTwist_comp_varpi_eq_of_mem_span_of_hasKernelOfDegree
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace P2mQU

open MvPowerSeries (subst HasSubst constantCoeff subst_comp_subst_apply subst_X hasSubst_of_constantCoeff_zero
  constantCoeff_subst_eq_zero constantCoeff_X)

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

section Dbl
variable {B : Type} [CommRing B]

noncomputable def inlX (B : Type) [CommRing B] : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)

noncomputable def inrX (B : Type) [CommRing B] : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)

noncomputable def dbl (φ : Series B) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) B :=
  Sum.elim (fun j => subst (inlX B) (φ j)) (fun j => subst (inrX B) (φ j))

theorem hasSubst_inlX : HasSubst (inlX B) := hasSubst_of_constantCoeff_zero (fun l => constantCoeff_X _)
theorem hasSubst_inrX : HasSubst (inrX B) := hasSubst_of_constantCoeff_zero (fun l => constantCoeff_X _)

theorem constantCoeff_dbl {φ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    ∀ s, constantCoeff (dbl φ s) = 0 := by
  rintro (j | j)
  · exact constantCoeff_subst_eq_zero hasSubst_inlX (fun l => constantCoeff_X _) (hφ j)
  · exact constantCoeff_subst_eq_zero hasSubst_inrX (fun l => constantCoeff_X _) (hφ j)

theorem hasSubst_dbl {φ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst (dbl φ) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_dbl hφ)

theorem hasSubst_series {φ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst φ :=
  hasSubst_of_constantCoeff_zero hφ

theorem dbl_comp {β ρ : Series B} (hβ : ∀ i, constantCoeff (β i) = 0) (hρ : ∀ i, constantCoeff (ρ i) = 0) :
    (fun s => subst (dbl ρ) (dbl β s)) = dbl (β.comp ρ) := by
  funext s
  rcases s with j | j
  · show subst (dbl ρ) (subst (inlX B) (β j)) = subst (inlX B) (subst ρ (β j))
    rw [subst_comp_subst_apply hasSubst_inlX (hasSubst_dbl hρ), subst_comp_subst_apply (hasSubst_series hρ) hasSubst_inlX]
    congr 1
    funext l
    rw [show inlX B l = MvPowerSeries.X (Sum.inl l) from rfl, subst_X (hasSubst_dbl hρ)]
    rfl
  · show subst (dbl ρ) (subst (inrX B) (β j)) = subst (inrX B) (subst ρ (β j))
    rw [subst_comp_subst_apply hasSubst_inrX (hasSubst_dbl hρ), subst_comp_subst_apply (hasSubst_series hρ) hasSubst_inrX]
    congr 1
    funext l
    rw [show inrX B l = MvPowerSeries.X (Sum.inr l) from rfl, subst_X (hasSubst_dbl hρ)]
    rfl

theorem cancel {ρ S S' : Series B}
    (hinj : ∀ H H' : MvPowerSeries (Fin 2) B, subst ρ H = subst ρ H' → H = H')
    (h : S.comp ρ = S'.comp ρ) : S = S' :=
  funext fun i => hinj _ _ (congrFun h i)

end Dbl

theorem sub_mem_span_of_isLawHom {B : Type} [CommRing B] [IsNoetherianRing B]
    (F F' : MvFormalGroup 2 B) (ρ ρ' : Series B)
    (hρ' : IsLawHom F F' ρ') (hle : ∀ j, ρ' j ∈ Ideal.span (Set.range ρ)) (i : Fin 2) :
    MvPowerSeries.subst F.toPowerSeries (ρ' i) -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ' i) ∈
      Ideal.span (Set.range fun j => MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j)) := by
  classical
  have hρ'0 : ∀ j, MvPowerSeries.constantCoeff (ρ' j) = 0 := hρ'.1
  apply MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
  intro C _ _ J m hJ s hs hS

  set sx : Fin 2 → C := fun l => s (Sum.inl l) with hsx
  set sz : Fin 2 → C := fun l => s (Sum.inr l) with hsz
  have hsx' : ∀ l, sx l ∈ J := fun l => hs _
  have hsz' : ∀ l, sz l ∈ J := fun l => hs _
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
  have hρ'z : ∀ j, MvFormalGroup.nilEval m (ρ' j) sz = 0 := fun j =>
    nilEval_eq_zero_of_mem_span J m hJ sz hsz' ρ hρz (hle j)

  rw [nilEval_sub, (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXl _).2, hevl,
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs F.toPowerSeries F.constantCoeff_eq_zero _).2]
  have huJ : ∀ j, MvFormalGroup.nilEval m (ρ' j) sx ∈ J :=
    (MvFormalGroup.nilEval_subst_of_mem J m hJ sx hsx' ρ' hρ'0 0).1

  have hlaw := hρ'.2 i
  have key := congrArg (fun G => MvFormalGroup.nilEval m G s) hlaw
  rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs F.toPowerSeries F.constantCoeff_eq_zero _).2] at key
  have hfam0 : ∀ t, MvPowerSeries.constantCoeff (Sum.elim
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ' j))
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ' j)) t) = 0 := by
    rintro (j | j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hXl) hXl (hρ'0 j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hXr) hXr (hρ'0 j)
  rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hfam0 _).2] at key
  have hinner : (fun t => MvFormalGroup.nilEval m (Sum.elim
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ' j))
      (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ' j)) t) s) =
      Sum.elim (fun j => MvFormalGroup.nilEval m (ρ' j) sx) (fun _ => 0) := by
    funext t
    rcases t with j | j
    · change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (ρ' j)) s = MvFormalGroup.nilEval m (ρ' j) sx
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXl _).2, hevl]
    · change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (ρ' j)) s = 0
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXr _).2, hevr]
      exact hρ'z j
  rw [hinner] at key

  have hunit : MvFormalGroup.nilEval m (F'.toPowerSeries i)
      (Sum.elim (fun j => MvFormalGroup.nilEval m (ρ' j) sx) (fun _ => 0)) =
      MvFormalGroup.nilEval m (ρ' i) sx := by
    have hfam1 : ∀ t : Fin 2 ⊕ Fin 2, MvPowerSeries.constantCoeff (Sum.elim (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin 2) B))
        (fun (_ : Fin 2) => (0 : MvPowerSeries (Fin 2) B)) t) = 0 := by
      rintro (j | j)
      · exact MvPowerSeries.constantCoeff_X _
      · exact map_zero _
    have h1 := (MvFormalGroup.nilEval_subst_of_mem J m hJ _ huJ _ hfam1 (F'.toPowerSeries i)).2
    rw [F'.subst_elim_X_zero i, MvFormalGroup.nilEval_X_of_mem J m hJ _ huJ i] at h1
    have hin2 : (fun t : Fin 2 ⊕ Fin 2 => MvFormalGroup.nilEval m (Sum.elim (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin 2) B))
        (fun (_ : Fin 2) => (0 : MvPowerSeries (Fin 2) B)) t) (fun j => MvFormalGroup.nilEval m (ρ' j) sx)) =
        Sum.elim (fun j => MvFormalGroup.nilEval m (ρ' j) sx) (fun _ => 0) := by
      funext t
      rcases t with j | j
      · exact MvFormalGroup.nilEval_X_of_mem J m hJ _ huJ j
      · exact nilEval_zero m _
    rw [hin2] at h1
    exact h1.symm
  rw [key, hunit, sub_self]

section Cancel
variable {B : Type} [CommRing B]

theorem isLawHom_of_comp_eq (F G G' : MvFormalGroup 2 B) (ρ ρ' u : Series B)
    (hρ : IsLawHom F G ρ) (hρ' : IsLawHom F G' ρ')
    (hinj2 : ∀ H H' : MvPowerSeries (Fin 2 ⊕ Fin 2) B,
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H' → H = H')
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (huρ : u.comp ρ = ρ') :
    IsLawHom G G' u := by
  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0 := hρ.1
  refine ⟨hu0, fun i => ?_⟩
  apply hinj2
  change MvPowerSeries.subst (dbl ρ) (MvPowerSeries.subst G.toPowerSeries (u i)) =
    MvPowerSeries.subst (dbl ρ) (MvPowerSeries.subst (dbl u) (G'.toPowerSeries i))
  have hρlaw : ∀ k, MvPowerSeries.subst F.toPowerSeries (ρ k) = MvPowerSeries.subst (dbl ρ) (G.toPowerSeries k) := hρ.2
  have hPlaw : MvPowerSeries.subst F.toPowerSeries (ρ' i) =
      MvPowerSeries.subst (dbl ρ') (G'.toPowerSeries i) := hρ'.2 i
  have huρi : MvPowerSeries.subst ρ (u i) = ρ' i := congrFun huρ i
  rw [MvPowerSeries.subst_comp_subst_apply G.hasSubst_toPowerSeries (hasSubst_dbl hρ0),
    MvPowerSeries.subst_comp_subst_apply (hasSubst_dbl hu0) (hasSubst_dbl hρ0), dbl_comp hu0 hρ0, huρ]
  have : (fun k => MvPowerSeries.subst (dbl ρ) (G.toPowerSeries k)) = fun k => MvPowerSeries.subst F.toPowerSeries (ρ k) :=
    funext fun k => (hρlaw k).symm
  rw [this, ← MvPowerSeries.subst_comp_subst_apply (hasSubst_series hρ0) F.hasSubst_toPowerSeries, huρi, hPlaw]

theorem comp_eq_comp_of_comp_eq (ρ ρ' u α β γ : Series B)
    (hinj : ∀ H H' : MvPowerSeries (Fin 2) B, MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H' → H = H')
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hα0 : ∀ i, MvPowerSeries.constantCoeff (α i) = 0) (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β i) = 0)
    (huρ : u.comp ρ = ρ') (hρα : ρ.comp α = β.comp ρ) (hρ'α : ρ'.comp α = γ.comp ρ') :
    u.comp β = γ.comp u := by
  apply cancel hinj
  rw [Series.comp_assoc _ _ _ hβ0 hρ0, ← hρα, ← Series.comp_assoc _ _ _ hρ0 hα0,
    huρ, hρ'α, ← huρ, ← Series.comp_assoc _ _ _ hu0 hρ0]

end Cancel

theorem isODHom_of_comp_eq {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
    (X Y Y' : FormalODModule p B) (ρ ρ' u : Series B)
    (hρ : FormalODModule.IsODHom X Y ρ) (hρ' : FormalODModule.IsODHom X Y' ρ')
    (hinj : ∀ H H' : MvPowerSeries (Fin 2) B, MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H' → H = H')
    (hinj2 : ∀ H H' : MvPowerSeries (Fin 2 ⊕ Fin 2) B,
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (ρ j))) H' → H = H')
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (huρ : u.comp ρ = ρ') :
    FormalODModule.IsODHom Y Y' u := by
  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0 := hρ.constantCoeff
  refine ⟨isLawHom_of_comp_eq X.F Y.F Y'.F ρ ρ' u hρ.1 hρ'.1 hinj2 hu0 huρ, fun a => ?_, ?_⟩
  · exact comp_eq_comp_of_comp_eq ρ ρ' u (X.act a) (Y.act a) (Y'.act a) hinj hρ0 hu0
      (X.isLawHom_act a).1 (Y.isLawHom_act a).1 huρ (hρ.2.1 a) (hρ'.2.1 a)
  · exact comp_eq_comp_of_comp_eq ρ ρ' u X.varpi Y.varpi Y'.varpi hinj hρ0 hu0
      X.isLawHom_varpi.1 Y.isLawHom_varpi.1 huρ hρ.2.2 hρ'.2.2

end P2mQU

open P2mQU in
theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (X Y : FormalODModule p B) (ψ : Series B) (hψ : FormalODModule.IsODHom X Y ψ)
    {d : ℕ} (hker : FormalODModule.HasKernelOfDegree X.varpi d)
    (hle : ∀ i, ψ i ∈ Ideal.span (Set.range X.varpi)) :
    ∃ χ : Series B,
      FormalODModule.IsODHom (FormalODModule.frobTwist X) Y χ ∧ χ.comp X.varpi = ψ ∧
      ∀ χ' : Series B, (∀ i, MvPowerSeries.constantCoeff (χ' i) = 0) → χ'.comp X.varpi = ψ → χ' = χ := by
  have hvp0 : ∀ i, MvPowerSeries.constantCoeff (X.varpi i) = 0 := X.isLawHom_varpi.1

  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree X.varpi hvp0 hker
  obtain ⟨hinj, hinj2, hdesc⟩ :=
    MvFormalGroup.subst_injective_and_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span
      X.F X.F X.varpi hvp0 X.isLawHom_varpi.2 ⟨N, hN⟩ hker.1 hker.2.1

  have hinv := fun i => sub_mem_span_of_isLawHom X.F Y.F X.varpi ψ hψ.1 hle i
  choose χ hχ using fun i => hdesc (ψ i) (hinv i)
  have hchi : Series.comp χ X.varpi = ψ := funext fun i => (hχ i).1.symm
  have hχ0 : ∀ i, MvPowerSeries.constantCoeff (χ i) = 0 := fun i => by
    rw [(hχ i).2]; exact hψ.constantCoeff i
  refine ⟨χ, ⟨isLawHom_of_comp_eq X.F X.F Y.F X.varpi ψ χ X.isLawHom_varpi hψ.1 hinj2 hχ0 hchi, fun a => ?_, ?_⟩,
    hchi, fun χ' _ hχ' => ?_⟩
  ·
    exact comp_eq_comp_of_comp_eq X.varpi ψ χ (X.act a) (X.act (WittVector.frobenius a)) (Y.act a) hinj hvp0 hχ0
      (X.isLawHom_act a).1 (X.isLawHom_act _).1 hchi (X.varpi_comp_act a) (hψ.2.1 a)
  ·
    exact comp_eq_comp_of_comp_eq X.varpi ψ χ X.varpi X.varpi Y.varpi hinj hvp0 hχ0 hvp0 hvp0 hchi rfl hψ.2.2
  ·
    exact cancel hinj (hχ'.trans hchi.symm)

end S_CerednikDrinfeld_FormalODModule_existsUnique_isODHom_frobTwist_comp_varpi_eq_of_mem_span_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_isODHom_frobTwist_comp_varpi_eq_of_mem_span_of_hasKernelOfDegree (solution)
