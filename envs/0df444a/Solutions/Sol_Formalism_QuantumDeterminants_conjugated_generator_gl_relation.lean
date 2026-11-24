-- Prove2me | solution 1 for Formalism.QuantumDeterminants.conjugated_generator_gl_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:56.528041+00:00
-- url     : https://prove2.me/submissions/29c51312-082a-4305-9575-b20dae991303

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_fun
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_smooth
import Theorems.Thm_Formalism_REAL_rdBracketV
import Theorems.Thm_Formalism_REAL_rdLinV
import Theorems.Thm_Formalism_REAL_rdSmoothV
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_commutator
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_sub
import Theorems.Thm_Formalism_REAL_vector_complexified_derivative_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : EabHGl := by
  intro n ε E _ _ H P Q f a b c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  rw [ioh_EabH_eq ε H P Q (EabH H c d f) a b hQP hPQ hH g, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q (EabH H a b f) c d hQP hPQ hH g, ioh_EabH_fun ε H P Q f a b hQP hPQ hH,
    vector_complexified_derivative_commutator rdLinV rdBracketV rdSmoothV ε _ _ _ _ hsm hg']
  have hQPX : ∀ X : Matrix (Fin n) (Fin n) ℂ, Q * (P * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  have hm2 : P * Matrix.single a b (1 : ℂ) * Q * (P * Matrix.single c d 1 * Q) -
      P * Matrix.single c d 1 * Q * (P * Matrix.single a b 1 * Q) =
      P * (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 -
        Matrix.single c d 1 * Matrix.single a b 1) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hQPX]
  rw [hm2, hm, Matrix.mul_sub, Matrix.sub_mul, vector_complexified_derivative_sub rdLinV hsm hg']
  split_ifs <;> simp only [Matrix.mul_zero, Matrix.zero_mul, vector_complexified_derivative_zero, sub_zero, zero_sub,
    ioh_EabH_eq ε H P Q f _ _ hQP hPQ hH g]
end Formalism.QuantumDeterminants
