-- Prove2me | solution 1 for DeletionCode.EditRigidity.shared_source_letters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:34.600016+00:00
-- url     : https://prove2.me/submissions/8ed6a2d2-5a95-4184-85e8-2810a2c433bd

import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_TwoEditWindows
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_EditRigidity
import Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_clean_block
import Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_origin_lt
import Theorems.Thm_DeletionCode_SingleEditOrigins_Edit_word_of_origin
import Theorems.Thm_DeletionCode_TwoEditWindows_exists_clean_block


set_option autoImplicit true
open DeletionCode DeletionCode.EditRigidity
open Windows HeaderRecovery SingleEditOrigins
namespace DeletionCode.EditRigidity
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (a b : ℕ) (ha : a + (windowLength k - 1) ≤ e.outputLength n)
    (hb : b + (windowLength k - 1) ≤ f.outputLength n)
    (hag : Agree (e.word x) a (f.word x) b (windowLength k - 1)) :
    ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ n ∧
      ∀ i, i < k →
        e.origin (a + s + i) = some (r + i) ∧
        f.origin (b + s + i) = some (r + i) := by
  have hL : windowLength k - 1 = 3 * k + 2 := by unfold windowLength; omega
  obtain ⟨s, hsk, hea, hfb⟩ := TwoEditWindows.exists_clean_block k a b e.cut f.cut
  obtain ⟨r, hr⟩ := e.clean_block a s k hea
  obtain ⟨r', hr'⟩ := f.clean_block b s k hfb
  have hrlast := e.origin_lt he (i := a + s + (k - 1)) (by omega)
    (hr (k - 1) (by omega))
  have hr'last := f.origin_lt hf (i := b + s + (k - 1)) (by omega)
    (hr' (k - 1) (by omega))
  have hri : r + k ≤ n := by omega
  have hr'i : r' + k ≤ n := by omega
  have hsource : Agree x r x r' k := by
    intro i hi
    have heq := hag (s + i) (by omega)
    calc
      x (r + i) = e.word x (a + s + i) := (e.word_of_origin x (hr i hi)).symm
      _ = f.word x (b + s + i) := by simpa only [Nat.add_assoc] using heq
      _ = x (r' + i) := f.word_of_origin x (hr' i hi)
  have hrr := hx r r' hri hr'i hsource
  subst r'
  exact ⟨s, r, by omega, hri, fun i hi => ⟨hr i hi, hr' i hi⟩⟩
end DeletionCode.EditRigidity
