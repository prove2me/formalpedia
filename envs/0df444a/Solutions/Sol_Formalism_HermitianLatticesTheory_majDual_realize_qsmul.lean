-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_realize_qsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:41.89622+00:00
-- url     : https://prove2.me/submissions/38dae4aa-75cb-489a-a498-8b307841c85b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_realize_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (q : ℚ) (x : V) : realize b X (algebraMap ℚ K q • x) = (q : ℝ) • realize b X x := by
  have hf : ∀ v : InfinitePlace K,
      fcoord b X v (algebraMap ℚ K q • x) = (q : ℂ) • fcoord b X v x := by
    intro v
    have hv : vecAt b v (algebraMap ℚ K q • x) = (q : ℂ) • vecAt b v x := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [vecAt]
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, eq_ratCast (algebraMap ℚ K) q,
        map_ratCast]
    rw [fcoord, fcoord, hv, Matrix.mulVec_smul]
  ext p
  rw [PiLp.smul_apply, majDual_realize_apply, majDual_realize_apply, hf]
  split_ifs <;> simp
end Formalism.HermitianLatticesTheory
