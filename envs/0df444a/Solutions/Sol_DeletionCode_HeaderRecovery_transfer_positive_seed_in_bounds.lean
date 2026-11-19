-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.transfer_positive_seed_in_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:57.328234+00:00
-- url     : https://prove2.me/submissions/b4097745-4a7c-4dfa-b202-f60a7dee6f7a

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbound : seed.offset + k ≤ positiveLength k h) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h := by
  cases ho : h.orientation with
  | deletion =>
    simp only [positiveLength, ho, shortLength, longLength, windowLength] at hbound
    by_cases hbefore : seed.offset + k ≤ editOffset k
    · simp only [transferPositiveSeed, ho, lengthenSeed, if_pos hbefore,
        negativeLength, longLength, windowLength]
      omega
    · by_cases hafter : editOffset k ≤ seed.offset
      · simp only [transferPositiveSeed, ho, lengthenSeed, if_neg hbefore,
          if_pos hafter, negativeLength, longLength, windowLength]
        omega
      · simp only [transferPositiveSeed, ho, lengthenSeed, if_neg hbefore,
          if_neg hafter, negativeLength, longLength, windowLength]
        omega
  | insertion =>
    simp only [positiveLength, ho, longLength, windowLength] at hbound
    by_cases hbefore : seed.offset + k ≤ editOffset k
    · simp only [transferPositiveSeed, ho, shortenSeed, if_pos hbefore,
        negativeLength, shortLength, longLength, windowLength]
      dsimp [editOffset, windowLength] at hbefore
      omega
    · by_cases hafter : editOffset k < seed.offset
      · simp only [transferPositiveSeed, ho, shortenSeed, if_neg hbefore,
          if_pos hafter, negativeLength, shortLength, longLength, windowLength]
        dsimp [editOffset, windowLength] at hafter
        omega
      · simp only [transferPositiveSeed, ho, shortenSeed, if_neg hbefore,
          if_neg hafter, negativeLength, shortLength, longLength, windowLength]
        dsimp [editOffset, windowLength] at hafter
        omega
end DeletionCode.HeaderRecovery
