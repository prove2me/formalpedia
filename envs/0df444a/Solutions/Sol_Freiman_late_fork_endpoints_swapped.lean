-- Prove2me | solution 1 for Freiman.late_fork_endpoints_swapped
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T11:18:44.829924+00:00
-- url     : https://prove2.me/submissions/3b3b41ea-b3c9-4b18-bcc1-cfe004d2a2a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Freiman_lateGeometry
import Theorems.Thm_Freiman_lowerEndpoint_swap_tie
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem child_digit (q : LowerPair) (d : ℕ+) :
    lowerChild q ([d], []) =
      ((lowerNormalize q).1 ++ [d], (lowerNormalize q).2) := by
  unfold lowerChild
  simp [List.reverse_cons, List.reverse_nil]

private theorem fork_words_true (n : LateNormalization) (d : ℕ+)
    (hw : n.wide = true) :
    lateForkWords n d = (n.label.1.reverse, n.label.2 ++ [d]) := by
  unfold lateForkWords lateWords lowerHistorySet lowerHistoryPick
  simp [hw]

private theorem equalWords_pos (q : LowerPair) (u : Bool)
    (hw : lowerWidth q.2 ≤ lowerWidth q.1)
    {s1 s2 : Bool}
    (h1 : lowerNaturalShort q.1 u = s1)
    (h2 : lowerNaturalShort q.2 u = s2) :
    lowerEqualWords q u =
      let e : List ℕ+ := if (q.1.length % 2 = 0) = (!u) then [3] else [1,3]
      let shorten := !s1 && !s2 &&
        decide (lowerWidth (q.1 ++ e) ≤ (7 / 5 : ℝ) * lowerWidth (q.2 ++ e))
      (q.1 ++ lowerEndpointSuffix q.1 u s1,
       q.2 ++ lowerEndpointSuffix q.2 u (s2 || shorten)) := by
  unfold lowerEqualWords
  have hN : lowerNormalize q = q := by
    unfold lowerNormalize
    simp [hw]
  simp [hN, hw, h1, h2]

private theorem equalWords_neg (q : LowerPair) (u : Bool)
    (hw : ¬ lowerWidth q.2 ≤ lowerWidth q.1)
    {s1 s2 : Bool}
    (h1 : lowerNaturalShort q.1 u = s1)
    (h2 : lowerNaturalShort q.2 u = s2) :
    lowerEqualWords q u =
      let e : List ℕ+ := if (q.2.length % 2 = 0) = (!u) then [3] else [1,3]
      let shorten := !s2 && !s1 &&
        decide (lowerWidth (q.2 ++ e) ≤ (7 / 5 : ℝ) * lowerWidth (q.1 ++ e))
      (q.1 ++ lowerEndpointSuffix q.1 u (s1 || shorten),
       q.2 ++ lowerEndpointSuffix q.2 u s2) := by
  unfold lowerEqualWords
  have hN : lowerNormalize q = (q.2, q.1) := by
    unfold lowerNormalize
    simp [hw]
  simp [hN, hw, h1, h2]

private theorem equalWords_swap_nontie (a b : List ℕ+) (u : Bool)
    (hpar : a.length % 2 = b.length % 2)
    (hne : lowerWidth a ≠ lowerWidth b) :
    lowerEqualWords (a, b) u =
      ((lowerEqualWords (b, a) u).2, (lowerEqualWords (b, a) u).1) := by
  generalize hsa : lowerNaturalShort a u = sa
  generalize hsb : lowerNaturalShort b u = sb
  by_cases hle : lowerWidth b ≤ lowerWidth a
  · have hlt : ¬ lowerWidth a ≤ lowerWidth b := by
      intro h; exact hne (le_antisymm h hle)
    have hpos := equalWords_pos (a, b) u hle hsa hsb
    have hneg := equalWords_neg (b, a) u hlt hsb hsa
    have heq :
        ((a.length % 2 = 0) = (!u)) = ((a.length % 2 = 0) = (!u)) := rfl
    simp [hpos, hneg, hpar]
  · have hle' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hle
    have hneg := equalWords_neg (a, b) u hle hsa hsb
    have hpos := equalWords_pos (b, a) u hle' hsb hsa
    simp [hneg, hpos, hpar]

private theorem naturalWords_swap (a b : List ℕ+) (u : Bool) :
    lowerNaturalWords (a, b) u =
      ((lowerNaturalWords (b, a) u).2, (lowerNaturalWords (b, a) u).1) := by
  unfold lowerNaturalWords
  rfl

private theorem virtual_left (a b : List ℕ+) (u : Bool)
    (hmix : a.length % 2 ≠ b.length % 2)
    (hle : lowerWidth b ≤ lowerWidth a)
    (hv : u = decide (a.length % 2 = 0)) :
    lowerEndpointWords (a, b) u = lowerEqualWords (a ++ [1], b) u := by
  unfold lowerEndpointWords
  have hne : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hmix
  simp [hne, hle, hv]

private theorem virtual_right (a b : List ℕ+) (u : Bool)
    (hmix : a.length % 2 ≠ b.length % 2)
    (hle : ¬ lowerWidth b ≤ lowerWidth a)
    (hv : u = decide (b.length % 2 = 0)) :
    lowerEndpointWords (a, b) u = lowerEqualWords (a, b ++ [1]) u := by
  unfold lowerEndpointWords
  have hne : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hmix
  simp [hne, hle, hv]

private theorem mixed_real_left (a b : List ℕ+) (u : Bool)
    (hmix : a.length % 2 ≠ b.length % 2)
    (hle : lowerWidth b ≤ lowerWidth a)
    (hv : u = decide (a.length % 2 = 0)) :
    lowerEndpoint (a, b) u = lowerEndpoint (a ++ [1], b) u := by
  unfold lowerEndpoint
  rw [virtual_left a b u hmix hle hv]
  have heq : ((a ++ [1], b).1.length % 2 = (a ++ [1], b).2.length % 2) := by
    have hlen : (a ++ [(1 : ℕ+)]).length = a.length + 1 := by simp
    rcases Nat.mod_two_eq_zero_or_one a.length with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.length with hb | hb <;>
        (try omega) <;> simp [hlen, Nat.add_mod, ha, hb] at hmix ⊢
  unfold lowerEndpointWords
  rw [if_pos heq]

private theorem mixed_real_right (a b : List ℕ+) (u : Bool)
    (hmix : a.length % 2 ≠ b.length % 2)
    (hle : ¬ lowerWidth b ≤ lowerWidth a)
    (hv : u = decide (b.length % 2 = 0)) :
    lowerEndpoint (a, b) u = lowerEndpoint (a, b ++ [1]) u := by
  unfold lowerEndpoint
  rw [virtual_right a b u hmix hle hv]
  have heq : ((a, b ++ [1]).1.length % 2 = (a, b ++ [1]).2.length % 2) := by
    have hlen : (b ++ [(1 : ℕ+)]).length = b.length + 1 := by simp
    rcases Nat.mod_two_eq_zero_or_one a.length with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b.length with hb | hb <;>
        (try omega) <;> simp [hlen, Nat.add_mod, ha, hb] at hmix ⊢
  unfold lowerEndpointWords
  rw [if_pos heq]

private theorem endpoint_of_swapped_words (a b : List ℕ+) (u : Bool)
    (h : lowerEndpointWords (a, b) u =
      ((lowerEndpointWords (b, a) u).2, (lowerEndpointWords (b, a) u).1)) :
    lowerEndpoint (a, b) u = lowerEndpoint (b, a) u := by
  simp [lowerEndpoint, h, add_comm, add_left_comm]

private theorem endpoint_swap_nontie (a b : List ℕ+) (u : Bool)
    (hne : lowerWidth a ≠ lowerWidth b) :
    lowerEndpoint (a, b) u = lowerEndpoint (b, a) u := by
  by_cases hpar : a.length % 2 = b.length % 2
  · refine endpoint_of_swapped_words a b u ?_
    unfold lowerEndpointWords
    have ha : (a, b).1.length % 2 = (a, b).2.length % 2 := hpar
    have hb : (b, a).1.length % 2 = (b, a).2.length % 2 := hpar.symm
    rw [if_pos ha, if_pos hb]
    exact equalWords_swap_nontie a b u hpar hne
  · by_cases hle : lowerWidth b ≤ lowerWidth a
    · have hlt : ¬ lowerWidth a ≤ lowerWidth b := by
        intro h; exact hne (le_antisymm h hle)
      by_cases hv : u = decide (a.length % 2 = 0)
      · by_cases hvt : lowerWidth (a ++ [1]) = lowerWidth b
        · have h1 := mixed_real_left a b u hpar hle hv
          have h2 := mixed_real_right b a u (fun h => hpar h.symm) hlt hv
          have h3 := lowerEndpoint_swap_tie (a ++ [1]) b u hvt
          exact h1.trans (h3.trans h2.symm)
        · refine endpoint_of_swapped_words a b u ?_
          unfold lowerEndpointWords
          have ha : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hpar
          have hb : ¬ ((b, a).1.length % 2 = (b, a).2.length % 2) :=
            fun h => hpar h.symm
          rw [if_neg ha, if_neg hb]
          simp [hle, hlt, hv]
          have hparV : (a ++ [1]).length % 2 = b.length % 2 := by
            have hlen : (a ++ [(1 : ℕ+)]).length = a.length + 1 := by simp
            rcases Nat.mod_two_eq_zero_or_one a.length with ha | ha <;>
              rcases Nat.mod_two_eq_zero_or_one b.length with hb | hb <;>
                (try omega) <;> simp [hlen, Nat.add_mod, ha, hb] at hpar ⊢
          simpa [hv] using equalWords_swap_nontie (a ++ [1]) b u hparV hvt
      · refine endpoint_of_swapped_words a b u ?_
        unfold lowerEndpointWords
        have ha : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hpar
        have hb : ¬ ((b, a).1.length % 2 = (b, a).2.length % 2) :=
          fun h => hpar h.symm
        rw [if_neg ha, if_neg hb]
        simp [hle, hlt, hv]
        exact naturalWords_swap a b u
    · have hle' : lowerWidth a ≤ lowerWidth b := le_of_not_ge hle
      have hlt : ¬ lowerWidth b ≤ lowerWidth a := hle
      by_cases hv : u = decide (b.length % 2 = 0)
      · by_cases hvt : lowerWidth a = lowerWidth (b ++ [1])
        · have h1 := mixed_real_right a b u hpar hle hv
          have h2 := mixed_real_left b a u (fun h => hpar h.symm) hle' hv
          have h3 := lowerEndpoint_swap_tie a (b ++ [1]) u hvt
          exact h1.trans (h3.trans h2.symm)
        · refine endpoint_of_swapped_words a b u ?_
          unfold lowerEndpointWords
          have ha : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hpar
          have hb : ¬ ((b, a).1.length % 2 = (b, a).2.length % 2) :=
            fun h => hpar h.symm
          rw [if_neg ha, if_neg hb]
          simp [hlt, hle', hv]
          have hparV : a.length % 2 = (b ++ [1]).length % 2 := by
            have hlen : (b ++ [(1 : ℕ+)]).length = b.length + 1 := by simp
            rcases Nat.mod_two_eq_zero_or_one a.length with ha | ha <;>
              rcases Nat.mod_two_eq_zero_or_one b.length with hb | hb <;>
                (try omega) <;> simp [hlen, Nat.add_mod, ha, hb] at hpar ⊢
          simpa [hv] using equalWords_swap_nontie a (b ++ [1]) u hparV hvt
      · refine endpoint_of_swapped_words a b u ?_
        unfold lowerEndpointWords
        have ha : ¬ ((a, b).1.length % 2 = (a, b).2.length % 2) := hpar
        have hb : ¬ ((b, a).1.length % 2 = (b, a).2.length % 2) :=
          fun h => hpar h.symm
        rw [if_neg ha, if_neg hb]
        simp [hlt, hle', hv]
        exact naturalWords_swap a b u

theorem solution (p : LowerPair) (path : LatePath)
    (hm : lateMatches p path.right3)
    (hv : latePathValid lateCatalog path)
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n)
    (n : LateNormalization) (hmem : n ∈ path.normalizations)
    (d : ℕ+) (hd : d ∈ ([1, 2] : List ℕ+)) (upper : Bool)
    (hw : n.wide = true) :
    lowerEndpoint (lowerChild (lowerChild p n.label) ([d], [])) upper =
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d))
        upper := by
  have := hm
  have := hv
  have := hd
  have hnorm := hn n hmem
  set N := lowerNormalize p
  set child := lowerChild p n.label
  have hchild : child = (N.1 ++ n.label.1.reverse, N.2 ++ n.label.2) := by
    unfold child N lowerChild
    rfl
  have hNchild : lowerNormalize child = (child.2, child.1) := by
    simpa [lateNormalizationHolds, child, hw] using hnorm
  have hL : lowerChild child ([d], []) = (child.2 ++ [d], child.1) := by
    rw [child_digit, hNchild]
  have hR : lowerHistoryAppend N (lateForkWords n d) =
      (child.1, child.2 ++ [d]) := by
    rw [fork_words_true n d hw, hchild]
    simp [lowerHistoryAppend, N]
  rw [hL, hR]
  by_cases htie : lowerWidth (child.2 ++ [d]) = lowerWidth child.1
  · exact lowerEndpoint_swap_tie (child.2 ++ [d]) child.1 upper htie
  · exact endpoint_swap_nontie (child.2 ++ [d]) child.1 upper htie
