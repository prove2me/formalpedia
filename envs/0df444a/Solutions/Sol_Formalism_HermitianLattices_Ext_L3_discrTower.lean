-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.discrTower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:29.245272+00:00
-- url     : https://prove2.me/submissions/ad45680c-b442-4631-982f-ec3d04109a9a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_finrank_eq_two
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_natAbs_discr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_discr_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution : DiscrTower := by
  intro K F _ _ _ _ _ _ hK hF
  have hpos := QuadraticExtensionConjugation.discr_pos hK hF
  have h1 := QuadraticExtensionConjugation.natAbs_discr hK hF
  have hTC : IsTotallyComplex K := by
    obtain ⟨h, -, -⟩ := hK
    exact h
  have hA : |(discr K : ℝ)| = (discr F : ℝ) ^ 2 := by
    have h2 := congrArg (fun n : ℕ => (n : ℝ)) h1
    simp only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at h2
    rw [h2, sq_abs]
  have hdeg : finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K := by
    have e1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have e2 := Module.finrank_mul_finrank ℚ F K
    have e3 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have e4 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
      first
        | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
        | exact IsTotallyComplex.nrRealPlaces_eq_zero
        | exact NumberField.InfinitePlace.nrRealPlaces_eq_zero_iff.mpr hTC
        | exact NumberField.nrRealPlaces_eq_zero_iff.mpr hTC
        | (haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} :=
             ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩
           simp [NumberField.InfinitePlace.nrRealPlaces])
        | (unfold NumberField.InfinitePlace.nrRealPlaces
           rw [Fintype.card_eq_zero_iff]
           exact ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩)
    rw [QuadraticExtensionConjugation.finrank_eq_two hK hF] at e2
    unfold Formalism.HermitianLatticesTheory.fDeg
    omega
  refine ⟨hA, hdeg, ?_⟩
  have hF0 : (0 : ℝ) < discr F := by exact_mod_cast hpos
  have hd : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    unfold Formalism.HermitianLatticesTheory.fDeg
    exact Fintype.card_pos
  have hd0 : ((Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring, hA, ← Real.rpow_natCast (discr F : ℝ) 2,
    ← Real.rpow_mul hF0.le, ← Real.rpow_natCast _ (Formalism.HermitianLatticesTheory.fDeg K), ← Real.rpow_mul hF0.le]
  conv_lhs => rw [← Real.rpow_one (discr F : ℝ)]
  congr 1
  first
    | (push_cast; field_simp)
    | (push_cast; field_simp; ring)
    | field_simp
    | (field_simp; ring)
end Formalism.HermitianLattices.Ext.L3
