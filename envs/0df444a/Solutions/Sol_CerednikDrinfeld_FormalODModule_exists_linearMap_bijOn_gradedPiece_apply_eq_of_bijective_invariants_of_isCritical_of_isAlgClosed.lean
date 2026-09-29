-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/26abcabe-2a0d-579f-9a58-b1373eb1e4bf

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
import Theorems.Thm_PadicInt_addMonoidHom_map_smul_of_free
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule

open scoped PadicInt Padic

namespace F2biAux

theorem isUnit_det_of_basis_mem_span_cols {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    (P : Submodule R M) (e' : Fin 2 → M) (he' : ∀ r, e' r ∈ P)
    (he'b : ∀ m ∈ P, ∃! w : Fin 2 → R, m = ∑ r, w r • e' r)
    (A : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ s, e' s ∈ Submodule.span R (Set.range fun t : Fin 2 => ∑ r, A r t • e' r)) :
    IsUnit A.det := by
  classical

  have hcoord : ∀ s, ∃ b : Fin 2 → R, e' s = ∑ t, b t • ∑ r, A r t • e' r := by
    intro s
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (h s)
    exact ⟨b, hb.symm⟩
  choose B hB using hcoord

  have hAB : ∀ s r, (∑ t, A r t * B s t) = if r = s then 1 else 0 := by
    intro s r
    have h1 : e' s = ∑ r, (∑ t, A r t * B s t) • e' r := by
      conv_lhs => rw [hB s]
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring_nf
    have h2 : e' s = ∑ r, (if r = s then (1 : R) else 0) • e' r := by
      simp [Finset.sum_ite_eq', ite_smul]
    obtain ⟨w, -, huniq⟩ := he'b (e' s) (he' s)
    have := (huniq _ h1).trans (huniq _ h2).symm
    exact congrFun this r
  have hmul : A * (Matrix.of fun t s => B s t) = 1 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hAB s r]
  exact Matrix.isUnit_det_of_right_inverse hmul

theorem isCompl_gradedSubmodule_succ {p : ℕ} [Fact p.Prime] {K : Type} [CommRing K]
    (j : Zp2 p →+* K) (X : FormalODModule p K) (hK : IsNilpotent (p : K)) (i : ℕ) :
    IsCompl (X.gradedSubmodule j i) (X.gradedSubmodule j (i + 1)) := by
  have h01 := CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j hK X
  rw [isCompl_gradedSubmodule_iff]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [show 2 * k = 0 + 2 * k by ring, FormalODModule.gradedPiece_add_two_mul,
      show 0 + 2 * k + 1 = 1 + 2 * k by ring, FormalODModule.gradedPiece_add_two_mul]
    exact h01
  · rw [show 2 * k + 1 = 1 + 2 * k by ring, FormalODModule.gradedPiece_add_two_mul,
      show 1 + 2 * k + 1 = 0 + 2 * (k + 1) by ring, FormalODModule.gradedPiece_add_two_mul]
    exact h01.symm

end F2biAux

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (i : ℕ) (hi : FormalODModule.CritChart.IsCritical X j i) (hi' : FormalODModule.CritChart.IsCritical X' j i)
    (θ₀ : FormalODModule.CritChart.invariants X j i →+ FormalODModule.CritChart.invariants X' j i)
    (hθ₀ : Function.Bijective θ₀) :
    ∃ Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F,
      Set.BijOn Θ (X.gradedPiece j i : Set (MvFormalGroup.CartierModule p X.F)) (X'.gradedPiece j i) ∧
      ∀ m : FormalODModule.CritChart.invariants X j i,
        Θ (m : MvFormalGroup.CartierModule p X.F) = ((θ₀ m : FormalODModule.CritChart.invariants X' j i) : MvFormalGroup.CartierModule p X'.F) := by
  classical

  obtain ⟨c, hcinj, hcfix⟩ := WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range p K
  have hcfix' : ∀ t : ℤ_[p], WittVector.frobenius (c t) = c t := fun t => (hcfix (c t)).2 ⟨t, rfl⟩
  have hK : IsNilpotent (p : K) := ⟨1, by rw [pow_one, CharP.cast_eq_zero]⟩

  let Xs : SpecialFormalODModule p j := ⟨X, hX, hX4⟩
  let Xs' : SpecialFormalODModule p j := ⟨X', hX', hX'4⟩
  obtain ⟨e, he_inv, he_basis, he_iff, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j Xs i hi
  obtain ⟨e', he'_inv, he'_basis, he'_iff, -, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j Xs' i hi'
  have he_mem : ∀ r, e r ∈ X.gradedPiece j i := fun r => (he_inv r).1
  have he'_mem : ∀ s, e' s ∈ X'.gradedPiece j i := fun s => (he'_inv s).1
  have hsum_mem : ∀ w : Fin 2 → WittVector p K, (∑ r, w r • e r) ∈ X.gradedPiece j i := fun w =>
    AddSubgroup.sum_mem _ fun r _ => smul_mem_gradedPiece X j i _ _ (he_mem r)
  have hsum_mem' : ∀ w : Fin 2 → WittVector p K, (∑ s, w s • e' s) ∈ X'.gradedPiece j i := fun w =>
    AddSubgroup.sum_mem _ fun s _ => smul_mem_gradedPiece X' j i _ _ (he'_mem s)

  have hlat : ∀ a : Fin 2 → ℤ_[p], (∑ r, c (a r) • e r) ∈ FormalODModule.CritChart.invariants X j i :=
    fun a => (he_iff _).2 fun r => hcfix' (a r)
  have hlat' : ∀ a : Fin 2 → ℤ_[p], (∑ s, c (a s) • e' s) ∈ FormalODModule.CritChart.invariants X' j i :=
    fun a => (he'_iff _).2 fun s => hcfix' (a s)
  have hlat_surj' : ∀ m ∈ FormalODModule.CritChart.invariants X' j i, ∃ a : Fin 2 → ℤ_[p], m = ∑ s, c (a s) • e' s := by
    intro m hm
    obtain ⟨w, hw, -⟩ := he'_basis m hm.1
    have hfix : ∀ s, WittVector.frobenius (w s) = w s := (he'_iff w).1 (hw ▸ hm)
    choose a ha using fun s => (hcfix (w s)).1 (hfix s)
    exact ⟨a, by rw [hw]; exact Finset.sum_congr rfl fun s _ => by rw [ha s]⟩
  have hlat_surj : ∀ m ∈ FormalODModule.CritChart.invariants X j i, ∃ a : Fin 2 → ℤ_[p], m = ∑ r, c (a r) • e r := by
    intro m hm
    obtain ⟨w, hw, -⟩ := he_basis m hm.1
    have hfix : ∀ r, WittVector.frobenius (w r) = w r := (he_iff w).1 (hw ▸ hm)
    choose a ha using fun r => (hcfix (w r)).1 (hfix r)
    exact ⟨a, by rw [hw]; exact Finset.sum_congr rfl fun r _ => by rw [ha r]⟩

  have huniq' : ∀ a b : Fin 2 → ℤ_[p], (∑ s, c (a s) • e' s) = ∑ s, c (b s) • e' s → a = b := by
    intro a b h
    have := (he'_basis _ (hsum_mem' fun s => c (a s))).unique rfl h
    funext s; exact hcinj (congrFun this s)

  have hα : ∀ a : Fin 2 → ℤ_[p], ∃ b : Fin 2 → ℤ_[p],
      ((θ₀ ⟨∑ r, c (a r) • e r, hlat a⟩ : FormalODModule.CritChart.invariants X' j i) : CartierModule p X'.F)
        = ∑ s, c (b s) • e' s := fun a => hlat_surj' _ (θ₀ ⟨_, hlat a⟩).2
  choose α hα using hα
  have hα_add : ∀ a b, α (a + b) = α a + α b := by
    intro a b
    apply huniq'
    rw [← hα]
    have hab : (⟨∑ r, c ((a + b) r) • e r, hlat (a + b)⟩ : FormalODModule.CritChart.invariants X j i)
        = ⟨∑ r, c (a r) • e r, hlat a⟩ + ⟨∑ r, c (b r) • e r, hlat b⟩ := by
      apply Subtype.ext
      show (∑ r, c ((a + b) r) • e r) = (∑ r, c (a r) • e r) + ∑ r, c (b r) • e r
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, map_add, add_smul]
    rw [hab, map_add, AddSubgroup.coe_add, hα, hα, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply, map_add, add_smul]
  let αh : (Fin 2 → ℤ_[p]) →+ (Fin 2 → ℤ_[p]) :=
    { toFun := α, map_zero' := by
        have := hα_add 0 0; rw [add_zero] at this
        exact left_eq_add.mp this |>.symm ▸ rfl, map_add' := hα_add }

  have hα_smul : ∀ (t : ℤ_[p]) (a : Fin 2 → ℤ_[p]), α (t • a) = t • α a :=
    fun t a => PadicInt.addMonoidHom_map_smul_of_free p αh t a
  let αl : (Fin 2 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
    { toFun := α, map_add' := hα_add, map_smul' := hα_smul }
  set A : Matrix (Fin 2) (Fin 2) ℤ_[p] := LinearMap.toMatrix' αl with hA
  have hAα : ∀ a, A.mulVec a = α a := by
    intro a; rw [hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  have hθA : ∀ a : Fin 2 → ℤ_[p],
      ((θ₀ ⟨∑ r, c (a r) • e r, hlat a⟩ : FormalODModule.CritChart.invariants X' j i) : CartierModule p X'.F)
        = ∑ s, c ((A.mulVec a) s) • e' s := by
    intro a; rw [hα, hAα]

  have hcols : ∀ a : Fin 2 → ℤ_[p],
      (∑ s, c ((A.mulVec a) s) • e' s) = ∑ r, c (a r) • ∑ s, (A.map c) s r • e' s := by
    intro a
    have h1 : ∀ s, c ((A.mulVec a) s) = ∑ r, c (a r) * (A.map c) s r := by
      intro s
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    simp_rw [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hmapvec : ∀ a : Fin 2 → ℤ_[p], (A.map c).mulVec (fun r => c (a r)) = fun s => c ((A.mulVec a) s) := by
    intro a; funext s
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

  have hdet : IsUnit (A.map c).det := by
    refine F2biAux.isUnit_det_of_basis_mem_span_cols (X'.gradedSubmodule j i) e' (fun s => he'_mem s)
      (fun m hm => he'_basis m hm) (A.map c) fun s => ?_
    obtain ⟨m, hm⟩ := hθ₀.2 ⟨e' s, he'_inv s⟩
    obtain ⟨b, hb⟩ := hlat_surj m.1 m.2
    have hms : m = ⟨∑ r, c (b r) • e r, hlat b⟩ := Subtype.ext hb
    have h1 : ((θ₀ m : FormalODModule.CritChart.invariants X' j i) : CartierModule p X'.F) = e' s := by
      rw [hm]
    have : e' s = ∑ r, c (b r) • ∑ t, (A.map c) t r • e' t := by
      rw [← h1, hms, hθA, hcols]
    rw [this]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have hAinv : (A.map c)⁻¹ * (A.map c) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hAinv' : (A.map c) * (A.map c)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  have hPc := F2biAux.isCompl_gradedSubmodule_succ j X hK i
  let lc : (Fin 2 → WittVector p K) →ₗ[WittVector p K] CartierModule p X.F :=
    Fintype.linearCombination (WittVector p K) e
  have hlc : ∀ w, lc w = ∑ r, w r • e r := fun w => Fintype.linearCombination_apply _ _ _
  let lcP : (Fin 2 → WittVector p K) →ₗ[WittVector p K] X.gradedSubmodule j i :=
    lc.codRestrict _ (fun w => by rw [hlc]; exact hsum_mem w)
  have hlcP : ∀ w, (lcP w : CartierModule p X.F) = ∑ r, w r • e r := fun w => hlc w
  have hbij : Function.Bijective lcP := by
    constructor
    · intro w₁ w₂ h
      have h' : (∑ r, w₁ r • e r) = ∑ r, w₂ r • e r := by
        rw [← hlcP, ← hlcP, h]
      exact (he_basis _ (hsum_mem w₁)).unique rfl h'
    · intro m
      obtain ⟨w, hw, -⟩ := he_basis m.1 m.2
      exact ⟨w, Subtype.ext (by rw [hlcP]; exact hw.symm)⟩
  let ε := LinearEquiv.ofBijective lcP hbij
  have hε : ∀ (m : X.gradedSubmodule j i) (w : Fin 2 → WittVector p K),
      (m : CartierModule p X.F) = ∑ r, w r • e r → ε.symm m = w := by
    intro m w hmw
    apply ε.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hmw]
    exact (hlcP w).symm
  let lc' : (Fin 2 → WittVector p K) →ₗ[WittVector p K] CartierModule p X'.F :=
    Fintype.linearCombination (WittVector p K) e'
  let Θ : CartierModule p X.F →ₗ[WittVector p K] CartierModule p X'.F :=
    lc' ∘ₗ (Matrix.mulVecLin (A.map c)) ∘ₗ ε.symm.toLinearMap ∘ₗ
      (Submodule.linearProjOfIsCompl (X.gradedSubmodule j i) (X.gradedSubmodule j (i + 1)) hPc)
  have hΘ : ∀ w : Fin 2 → WittVector p K, Θ (∑ r, w r • e r) = ∑ s, ((A.map c).mulVec w) s • e' s := by
    intro w
    have h1 : Submodule.linearProjOfIsCompl (X.gradedSubmodule j i) (X.gradedSubmodule j (i + 1)) hPc
        (∑ r, w r • e r) = ⟨_, hsum_mem w⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hPc ⟨_, hsum_mem w⟩
    show lc' ((A.map c).mulVecLin (ε.symm (Submodule.linearProjOfIsCompl _ _ hPc (∑ r, w r • e r)))) = _
    rw [h1, hε _ w rfl, Matrix.mulVecLin_apply, Fintype.linearCombination_apply]
  have hΘ_all : ∀ m, Θ m ∈ X'.gradedPiece j i := by
    intro m
    show lc' _ ∈ X'.gradedPiece j i
    rw [Fintype.linearCombination_apply]
    exact hsum_mem' _
  refine ⟨Θ, ⟨fun m _ => hΘ_all m, ?_, ?_⟩, ?_⟩
  · intro m₁ hm₁ m₂ hm₂ hΘeq
    obtain ⟨w₁, hw₁, -⟩ := he_basis m₁ hm₁
    obtain ⟨w₂, hw₂, -⟩ := he_basis m₂ hm₂
    rw [hw₁, hw₂, hΘ, hΘ] at hΘeq
    have h3 := (he'_basis _ (hsum_mem' ((A.map c).mulVec w₁))).unique rfl hΘeq
    have hw : w₁ = w₂ := by
      have := congrArg ((A.map c)⁻¹.mulVec) h3
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec, Matrix.one_mulVec] at this
    rw [hw₁, hw₂, hw]
  · intro m' hm'
    obtain ⟨v, hv, -⟩ := he'_basis m' hm'
    refine ⟨∑ r, ((A.map c)⁻¹.mulVec v) r • e r, hsum_mem _, ?_⟩
    rw [hΘ, Matrix.mulVec_mulVec, hAinv', Matrix.one_mulVec]
    exact hv.symm
  · intro m
    obtain ⟨a, ha⟩ := hlat_surj m.1 m.2
    have hm : m = ⟨∑ r, c (a r) • e r, hlat a⟩ := Subtype.ext ha
    rw [hm, hθA]
    show Θ (∑ r, c (a r) • e r) = _
    rw [hΘ, hmapvec]

end S_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_linearMap_bijOn_gradedPiece_apply_eq_of_bijective_invariants_of_isCritical_of_isAlgClosed (solution)
