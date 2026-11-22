-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_6_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:31:31.904678+00:00
-- url     : https://prove2.me/submissions/c962edd1-88ad-4663-a25d-911566b199bb

import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL

namespace DistLTLSynth.Char.Lemma613Aux
open DistLTLSynth.Char

lemma cylinder_isOpen (g : ℕ → CommGraph) (i : ℕ) :
    IsOpen {w : ℕ → CommGraph | ∀ k < i, w k = g k} := by
  have h : IsOpen (⋂ k ∈ Finset.range i, {w : ℕ → CommGraph | w k = g k}) :=
    isOpen_biInter_finset fun k _ => by
      have hc : Continuous (fun w : ℕ → CommGraph => w k) := continuous_apply k
      exact hc.isOpen_preimage {g k} (isOpen_discrete _)
  convert h using 1
  ext w
  simp only [Set.mem_iInter, Finset.mem_range]
  rfl

lemma pre_congr_of_lt {α : Type} {a b : ℕ → α} {r : ℕ} (hab : ∀ k < r, a k = b k) :
    pre a r = pre b r := by
  unfold pre
  congr 1
  funext j
  exact hab j.val j.isLt

lemma exec_congr_before {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2)
    {h h' : ℕ → Signal X1 X2} {i : ℕ} (hh : ∀ k < i, h' k = h k) :
    ∀ k < i, exec f h' k = exec f h k := by
  intro k hk
  unfold exec
  rw [hh k hk, pre_congr_of_lt (fun m hm => hh m (Nat.lt_of_lt_of_le hm (Nat.succ_le_of_lt hk)))]

lemma append_pre_shift_eq {α : Type} (x y : ℕ → α) (i : ℕ) (hxy : ∀ k < i, y k = x k) :
    append (pre x i) (fun m => y (m + i)) = y := by
  funext n
  unfold append
  have hlen : (pre x i).length = i := by simp [pre]
  by_cases hn : n < (pre x i).length
  · rw [dif_pos hn]
    have hni : n < i := hlen ▸ hn
    have hget : (pre x i)[n] = x n := by simp [pre]
    rw [hget, hxy n hni]
  · rw [dif_neg hn]
    have hge : i ≤ n := Nat.le_of_not_lt (hlen ▸ hn)
    dsimp only
    rw [hlen, Nat.sub_add_cancel hge]

end DistLTLSynth.Char.Lemma613Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma613Aux in
theorem solution {X1 X2 Y1 Y2 : Type} [Fintype X1] [Nonempty X1] [Fintype X2] [Nonempty X2]
    [Fintype Y1] [Nonempty Y1] [Fintype Y2] [Nonempty Y2]
    (A : Set (ℕ → CommGraph)) (φ : Formula X1 X2 Y1 Y2) (hφ : φ.IsSafety)
    (f : Algorithm X1 X2 Y1 Y2) :
    FRealizes f A φ ↔ FRealizes f (closure A) φ := by
  constructor
  · intro hf h hg
    by_contra hbad
    obtain ⟨i, hi⟩ := hφ (exec f h) hbad
    have hopen := cylinder_isOpen (graphOf h) i
    have hmem : graphOf h ∈ {w : ℕ → CommGraph | ∀ k < i, w k = graphOf h k} :=
      fun _ _ => rfl
    obtain ⟨w, hw_cyl, hwA⟩ := mem_closure_iff.mp hg _ hopen hmem
    let h' : ℕ → Signal X1 X2 := fun n => ((h n).1, (h n).2.1, w n)
    have hgraph : graphOf h' = w := rfl
    have hh' : ∀ k < i, h' k = h k := by
      intro k hk
      cases hnk : h k with
      | mk x1 rest =>
        cases rest with
        | mk x2 gk =>
          have hwk : w k = gk := by
            have := hw_cyl k hk
            simpa [graphOf, hnk] using this
          simp [h', hnk, hwk]
    have hexec : ∀ k < i, exec f h' k = exec f h k := exec_congr_before f hh'
    have happ := append_pre_shift_eq (exec f h) (exec f h') i hexec
    have hsat : exec f h' ∈ φ.Lang := hf h' (hgraph ▸ hwA)
    exact hi (fun m => exec f h' (m + i)) (happ.symm ▸ hsat)
  · intro hf h hg
    exact hf h (subset_closure hg)
