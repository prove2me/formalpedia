-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.commute_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:26:34.146167+00:00
-- url     : https://prove2.me/submissions/9fcd8455-c46d-45f5-80f9-2bd7f112890a

import Mathlib
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterF7

set_option autoImplicit false

namespace P30c9dbb5

open MvPolynomial in
theorem pderiv_comm {d : ℕ} (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, pderiv_X]
    rcases eq_or_ne j i with rfl | hj <;> rcases eq_or_ne k j with rfl | hk
    · rfl
    · have hk' : j ≠ k := fun h => hk h.symm
      simp [Pi.single_apply, hk, hk']
      ring
    · rfl
    · rcases eq_or_ne k i with rfl | hki
      · have hj' : k ≠ j := hk
        simp [Pi.single_apply, hj, hj', hj.symm]
        ring
      · simp [Pi.single_apply, hj, hki, hj.symm, hki.symm]

open MvPolynomial BookProof.YangMillsHermite in
theorem key {d : ℕ} (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    BookProof.YangMillsHermite.momOp j (BookProof.YangMillsHermite.momOp k p)
      = BookProof.YangMillsHermite.momOp k (BookProof.YangMillsHermite.momOp j p) := by
  classical
  simp only [BookProof.YangMillsHermite.momOp, BookProof.YangMillsHermite.derOp,
    BookProof.YangMillsHermite.mulOp, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, map_smul, map_sub]
  by_cases hjk : j = k
  · subst hjk; rfl
  · have hkj : k ≠ j := fun h => hjk h.symm
    simp [hjk, hkj, smul_sub, pderiv_X, Pi.single_apply]
    rw [pderiv_comm j k p]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring

end P30c9dbb5

open BookProof.ChapterF7 BookProof.QuantumGravity3DGauge BookProof.YangMillsHermite in
theorem solution {d : ℕ} (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j (momOp k p) = momOp k (momOp j p) := by
  exact P30c9dbb5.key j k p
