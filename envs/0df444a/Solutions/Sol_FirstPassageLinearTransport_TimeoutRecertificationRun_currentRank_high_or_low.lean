-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_high_or_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:28.209659+00:00
-- url     : https://prove2.me/submissions/d7bfe0b7-ff90-454e-a150-934c44e32713

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    (∃ m : ℕ, S ≤ m ∧ q = rationalTargetRank P.rHi m) ∨
      (∃ m : ℕ, L ≤ m ∧ q = timeoutTargetRank K₀ L m) := by
  cases hrun with
  | first hSM hM0 hnShell hnGood =>
      exact Or.inl ⟨M, hSM, rfl⟩
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap =>
      exact Or.inl ⟨_, hSm, rfl⟩
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos
      hqparent hgap =>
      exact Or.inr ⟨_, hLm, rfl⟩
end TimeoutRecertificationRun
end FirstPassageLinearTransport
