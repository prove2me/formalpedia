-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.poly_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:06.072227+00:00
-- url     : https://prove2.me/submissions/1771a2f3-1a2b-4d38-a615-7022652e0dbd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open Formalism.L2.Th1.D.TraceNormBounds
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution (l : ℕ) (hl : l.Prime) : ∃ Q : Polynomial ℤ,
    (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
      (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = Polynomial.C (l : ℤ) * Q := by
  have : Fact l.Prime := ⟨hl⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  have hprod : ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) =
      (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)) := by
    have hr := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rw [ZMod.card] at hr
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod l) hl.one_lt
    have hmon : (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hl.one_lt
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hr, hdeg]; simp)
    rw [hr] at h
    exact h
  have hrange : ∏ n ∈ Finset.range l, (Polynomial.X - ((n : ℕ) : Polynomial (ZMod l))) =
      ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) := by
    refine Finset.prod_bij (fun n _ => ((n : ℕ) : ZMod l)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      (fun _ _ => by rw [map_natCast])
    · intro a ha b hb hab
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.1 ha),
        ZMod.val_natCast_of_lt (Finset.mem_range.1 hb)] at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), by simp⟩
  change Polynomial.C (l : ℤ) ∣ _
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : Polynomial.map (Int.castRingHom (ZMod l))
      (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
        (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_natCast]
    rw [hrange, hprod, sub_self]
  have h := congrArg (fun P => Polynomial.coeff P i) hmap
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
  exact h
end Formalism.L2.Th1.D.TraceNormBounds
