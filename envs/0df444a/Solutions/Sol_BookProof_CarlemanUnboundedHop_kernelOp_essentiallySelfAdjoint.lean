-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.kernelOp_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:01:18.351993+00:00
-- url     : https://prove2.me/submissions/450bb486-7a99-488e-af05-a6095c9ca8fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.kernelOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_kernelOp_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow
open BookProof.FarisLavine
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp hk) :=
  ⟨kernelOp_deficiencyTrivialAt hk hθ0 hΘ hΘsum hApos hAmono hbd hcar (by simp),
      kernelOp_deficiencyTrivialAt hk hθ0 hΘ hΘsum hApos hAmono hbd hcar (by simp)⟩
