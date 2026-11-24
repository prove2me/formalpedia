-- Prove2me | solution 1 for Formalism.DivisionValues.covolume_via_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:26.696657+00:00
-- url     : https://prove2.me/submissions/53d121bb-5435-42a0-9b57-3574ae816f41

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_exists_int_mul
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues
open LocalCovolumeBasis
namespace Formalism.DivisionValues
theorem _root_.solution : LcvBasis := by
  intro K _ _ _ _ d X hX L hL e he
  classical
  set E := Submodule.span (𝓞 K) (Set.range e) with hEdef
  have hLfg : L.FG := hL.fg
  have hLsp : Submodule.span K (L : Set (Fin d → K)) = ⊤ := hL.span_eq_top
  obtain ⟨y, hy0, hyL⟩ := exists_int_mul L hLsp e
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.mpr hy0
  set e' : Fin d → Fin d → K := fun i => (y : K) • e i with he'def
  have he' : LinearIndependent K e' := by
    have := he.units_smul (fun _ => Units.mk0 (y : K) hyK)
    convert this using 1
    funext i
    simp [e', Units.smul_def]
  set E' := Submodule.span (𝓞 K) (Set.range e') with hE'def
  have hE'L : E' ≤ L := Submodule.span_le.mpr (Set.range_subset_iff.mpr hyL)
  have hE'E : E' ≤ E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    show (y : K) • e i ∈ E
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) y
  have hEfg : E.FG := Submodule.fg_span (Set.finite_range e)
  have hE'fg : E'.FG := Submodule.fg_span (Set.finite_range e')
  have hrkL : Formalism.HN.rkK L = d := by
    unfold Formalism.HN.rkK; rw [hLsp, finrank_top, Module.finrank_fin_fun]
  have hrkE : Formalism.HN.rkK E = d := by
    unfold Formalism.HN.rkK
    rw [hEdef, Submodule.span_span_of_tower, finrank_span_eq_card he, Fintype.card_fin]
  obtain ⟨hG1, -⟩ := Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he
  obtain ⟨-, hG2⟩ :=
    Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e' he'
  have h1 := hG2 L hLfg hE'L hrkL
  have h2 := hG2 E hEfg hE'E hrkE
  have hpos : ∀ M : Submodule (𝓞 K) (Fin d → K), M.FG →
      0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    fun M hM => (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hM).2.2
  set rL := E'.toAddSubgroup.relIndex L.toAddSubgroup with hrL
  set rE := E'.toAddSubgroup.relIndex E.toAddSubgroup with hrE
  have hrL0 : rL ≠ 0 := by
    intro h
    have := hpos E' hE'fg
    rw [← h1, h, Nat.cast_zero, mul_zero] at this
    exact lt_irrefl _ this
  have hrE0 : rE ≠ 0 := by
    intro h
    have := hpos E' hE'fg
    rw [← h2, h, Nat.cast_zero, mul_zero] at this
    exact lt_irrefl _ this
  obtain ⟨lenL, suppL, logL⟩ := key L rL E' hE'L rfl hrL0
  obtain ⟨lenE, suppE, logE⟩ := key E rE E' hE'E rfl hrE0
  have hidx : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w E L = (locLen w.asIdeal E E' : ℤ) - locLen w.asIdeal L E' :=
    fun w => indexBasic_lidx_via w.asIdeal E L E' hE'E hE'L (lenE w) (lenL w)
  have hn : (finrank ℚ K : ℝ) ≠ 0 := (Nat.cast_pos.mpr Module.finrank_pos).ne'
  set fE := fun w : HeightOneSpectrum (𝓞 K) =>
    Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal E E' : ℝ) with hfEdef
  set fL := fun w : HeightOneSpectrum (𝓞 K) =>
    Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal L E' : ℝ) with hfLdef
  have hpt : (fun w => lw w * (idx w E L : ℝ)) =
      fun w => (fE w - fL w) * (1 / (finrank ℚ K : ℝ)) := by
    funext w
    rw [hidx w]
    simp only [lw, fE, fL]
    push_cast
    field_simp
  have hfE : (Function.support fE).Finite := by
    apply suppE.subset
    intro w hw h
    apply hw
    simp [fE, h]
  have hfL : (Function.support fL).Finite := by
    apply suppL.subset
    intro w hw h
    apply hw
    simp [fL, h]
  refine ⟨?_, ?_⟩
  · rw [hpt]
    apply (hfE.union hfL).subset
    intro w hw
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    apply hw
    simp only
    rw [hcon.1, hcon.2]
    simp
  · unfold lcv
    rw [hpt, ← finsum_mul, finsum_sub_distrib hfE hfL, ← logE, ← logL]
    have hlogL : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L) =
        Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E') - Real.log (rL : ℝ) := by
      rw [← h1, Real.log_mul (hpos L hLfg).ne' (Nat.cast_ne_zero.mpr hrL0)]
      ring
    have hlogE : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E) =
        Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E') - Real.log (rE : ℝ) := by
      rw [← h2, Real.log_mul (hpos E hEfg).ne' (Nat.cast_ne_zero.mpr hrE0)]
      ring
    have hdet : Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X E) =
        ∑ v, Real.log (gram X v e).det.re := by
      have hne := (hpos E hEfg).ne'
      rw [hG1] at hne ⊢
      exact Real.log_prod fun v hv => Finset.prod_ne_zero_iff.mp hne v hv
    rw [hlogL, ← hdet]
    field_simp
    linarith [hlogE]
end Formalism.DivisionValues
