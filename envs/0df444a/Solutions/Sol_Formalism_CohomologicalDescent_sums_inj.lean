-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sums_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:48.794283+00:00
-- url     : https://prove2.me/submissions/24028318-7126-49ee-ae99-bc8f59efa9fa

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution (D h : ℕ) (L : ℝ) (hD : 1 ≤ D) (hDh : D ≤ h) (hh : (h : ℝ) < L ^ 2)
    (hL : 1 ≤ L) (l l' : ℕ) (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ))
    (hLl' : L < (l' : ℝ)) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))
    (heq : d0 l (D : ℤ) = d0 l' (D : ℤ)) : l = l' := by
  by_contra hne
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  obtain ⟨_, hdvd', _⟩ := leastCongruentPos_mem_le l' D hD
  rw [← heq] at hdvd'
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').2 hne
  have hprod := hcop.mul_dvd hdvd hdvd'
  have hpos : (0 : ℤ) < (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by omega
  have hle2 := Int.le_of_dvd hpos hprod
  have hZ : (l : ℤ) * (l' : ℤ) ≤ (h : ℤ) := by
    have : (D : ℤ) ≤ h := by exact_mod_cast hDh
    have : (0 : ℤ) ≤ (d0 l (D : ℤ) : ℤ) := by positivity
    linarith
  have hR : (l : ℝ) * (l' : ℝ) ≤ (h : ℝ) := by exact_mod_cast hZ
  have hL0 : 0 ≤ L := by linarith
  have : L ^ 2 < (l : ℝ) * (l' : ℝ) := by
    rw [sq]; exact mul_lt_mul'' hLl hLl' hL0 hL0
  linarith
end Formalism.CohomologicalDescent
