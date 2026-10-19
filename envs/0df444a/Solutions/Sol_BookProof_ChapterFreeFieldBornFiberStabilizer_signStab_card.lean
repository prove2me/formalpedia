-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:41.108982+00:00
-- url     : https://prove2.me/submissions/a5bae967-f325-4a84-b611-10077663d783

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — solution of BookProof.ChapterFreeFieldBornFiberStabilizer.signStab_card
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberStabilizer



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x : EuclideanSpace ℝ (Fin n)) :
    (signStab x).card = 2 ^ (Finset.univ.filter (fun k => x k = 0)).card := by

      -- The stabilizer of `x` under the sign gauge has `2 ^ (#zero coordinates)` elements: the sign
      -- choices on the vanishing coordinates are free, while the nonzero coordinates are forced to
      -- `+1`.
      have h_stabilizer : signStab x = Finset.univ.filter (fun b : Fin n → Bool => ∀ k, x k ≠ 0 → b
          k = true) := by
        ext b;
        simp [ mem_signStab ];
      rw [ h_stabilizer, show ( Finset.univ.filter fun b : Fin n → Bool => ∀ k : Fin n, x.ofLp k ≠ 0
          → b k = true ) = Finset.image ( fun b : Finset ( Fin n ) => fun k => if k ∈ b then false
              else true ) ( Finset.powerset ( Finset.univ.filter fun k => x.ofLp k = 0 ) ) from ?_,
                  Finset.card_image_of_injective ];
      · rw [ Finset.card_powerset ];
      · intro a b h; ext k; have hk2 := congr_fun h k
        by_cases hk : k ∈ a <;> by_cases hk' : k ∈ b <;> simp_all
      · ext b; simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Bool.if_true_right,
          Bool.or_false, Finset.mem_image, Finset.mem_powerset];
        constructor;
        · intro hb; use Finset.univ.filter (fun k => b k = false); simp_all ;
          intro k hkb
          simp at hkb
          by_contra hnz
          simp at hnz
          have := hb k hnz
          rw [hkb] at this
          exact Bool.noConfusion this
        · rintro ⟨ a, ha, rfl ⟩ k hk; specialize ha; replace ha := @ha k; aesop;
