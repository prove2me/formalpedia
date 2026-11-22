-- Prove2me | solution 1 for ContiguousCake597.Approximate.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:26:25.568892+00:00
-- url     : https://prove2.me/submissions/45ee8b66-7dc4-4e51-9c2e-1d66230576bc

import Definitions.Def_ContiguousCake597_Approximate_Analysis

set_option autoImplicit false

namespace ContiguousCake597.Approximate.LocalizationProof

theorem overlap_nonneg (x y c d : ℝ) : 0 ≤ overlap x y c d := le_max_left _ _

theorem overlap_le_interval (x y c d : ℝ) (hcd : c ≤ d) :
    overlap x y c d ≤ d - c := by
  apply max_le (sub_nonneg.mpr hcd)
  exact sub_le_sub (min_le_right _ _) (le_max_right _ _)

theorem R_ge (G : HZTractability.ThrGraph) : 32 ≤ R G := by
  unfold R
  omega

theorem a_separated (G : HZTractability.ThrGraph) (u v : Fin G.n) (huv : u ≠ v) :
    a G u + 1 < a G v ∨ a G v + 1 < a G u := by
  have hR := R_ge G
  have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_right (R G) (show u.val + 1 + 1 ≤ v.val + 1 by omega)
    have hgap : a G u + R G ≤ a G v := by
      simpa only [a, Nat.add_mul, Nat.one_mul] using hmul
    exact Or.inl (by omega)
  · have hmul := Nat.mul_le_mul_right (R G) (show v.val + 1 + 1 ≤ u.val + 1 by omega)
    have hgap : a G v + R G ≤ a G u := by
      simpa only [a, Nat.add_mul, Nat.one_mul] using hmul
    exact Or.inr (by omega)

theorem boundary_unique (G : HZTractability.ThrGraph) (i : Fin (N G))
    (u v : Fin G.n)
    (hu : i.val + 1 = a G u ∨ i.val + 1 = a G u + 1)
    (hv : i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) : u = v := by
  by_contra hne
  rcases a_separated G u v hne with h | h <;> rcases hu with hu | hu <;>
    rcases hv with hv | hv <;> omega

theorem sum_filter_map {α : Type*} (xs : List α) (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    ((xs.filter (fun x => decide (P x))).map f).sum =
      (xs.map (fun x => if P x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : P x <;> simp [hx, ih]

theorem boundary_sum_le (G : HZTractability.ThrGraph) (i : Fin (N G)) (x y : ℝ) :
    (((List.finRange G.n).filter
      (fun v => i.val + 1 = a G v ∨ i.val + 1 = a G v + 1)).map
      (fun v => overlap x y ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ))).sum ≤ 1 := by
  rw [sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
  have hcount : (∑ v : Fin G.n,
      if i.val + 1 = a G v ∨ i.val + 1 = a G v + 1 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hex : ∃ v : Fin G.n, i.val + 1 = a G v ∨ i.val + 1 = a G v + 1
    · obtain ⟨v, hv⟩ := hex
      have hp (u : Fin G.n) :
          (i.val + 1 = a G u ∨ i.val + 1 = a G u + 1) ↔ u = v := by
        exact ⟨fun hu => boundary_unique G i u v hu hv, fun h => h ▸ hv⟩
      simp only [hp]
      simp
    · have hp (v : Fin G.n) : ¬ (i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) :=
        fun hv => hex ⟨v, hv⟩
      rw [Finset.sum_eq_zero (fun v _ => if_neg (hp v))]
      norm_num
  apply le_trans (Finset.sum_le_sum ?_) hcount
  intro v _
  split_ifs
  · have hlen : ((boundary G v).2 : ℝ) - ((boundary G v).1 : ℝ) = 1 := by
      simp only [boundary]
      push_cast
      ring
    have hvalid : ((boundary G v).1 : ℝ) ≤ ((boundary G v).2 : ℝ) := by linarith
    simpa only [hlen] using overlap_le_interval x y _ _ hvalid
  · exact le_rfl

theorem centered_overlap_le (G : HZTractability.ThrGraph) (j : ℕ) (r : ℚ)
    (hr : 0 ≤ r) (x y : ℝ) :
    overlap x y ((centered G j r).1 : ℝ) ((centered G j r).2 : ℝ) ≤ (r : ℝ) := by
  have hlen : ((centered G j r).2 : ℝ) - ((centered G j r).1 : ℝ) = r := by
    simp only [centered]
    push_cast
    ring
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hvalid : ((centered G j r).1 : ℝ) ≤ ((centered G j r).2 : ℝ) := by linarith
  simpa only [hlen] using overlap_le_interval x y _ _ hvalid

theorem ownBonus_bounds (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    0 ≤ ownBonus G i ∧ ownBonus G i ≤ 3 := by
  unfold ownBonus
  split_ifs <;> norm_num

theorem nextBonus_bounds (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    0 ≤ nextBonus G i ∧ nextBonus G i ≤ 3 := by
  unfold nextBonus
  split_ifs <;> norm_num

theorem bonus_bound (G : HZTractability.ThrGraph) (i : Fin (N G)) (x y : ℝ) :
    0 ≤ U G i x y - (y - x) ∧ U G i x y - (y - x) ≤ 6 := by
  have hnonneg : 0 ≤ ((bonuses G i).map
      (fun ab => overlap x y (ab.1 : ℝ) (ab.2 : ℝ))).sum := by
    apply List.sum_nonneg
    intro r hr
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hr
    exact overlap_nonneg _ _ _ _
  refine ⟨by simpa only [U, add_sub_cancel_left] using hnonneg, ?_⟩
  have hown := centered_overlap_le G (i.val + 1) (ownBonus G i) (ownBonus_bounds G i).1 x y
  have hnext := centered_overlap_le G ((pi G i).val + 1) (nextBonus G i)
    (nextBonus_bounds G i).1 x y
  have hboundary := boundary_sum_le G i x y
  simp only [U, bonuses, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def] at *
  by_cases hfollowing : ∃ v : Fin G.n, i.val + 1 = a G v + 1
  · have hownval : ownBonus G i = 2 := by rw [ownBonus, if_pos hfollowing]
    have hnextval : (nextBonus G i : ℝ) ≤ 3 := by exact_mod_cast (nextBonus_bounds G i).2
    have howncast : (ownBonus G i : ℝ) = 2 := by exact_mod_cast hownval
    linarith only [hown, howncast, hnext, hnextval, hboundary]
  · by_cases hspecial : ∃ v : Fin G.n, i.val + 1 = a G v
    · have hownval : ownBonus G i = 5/2 := by
        rw [ownBonus, if_neg hfollowing, if_pos hspecial]
      have hnextval : nextBonus G i = 5/2 := by rw [nextBonus, if_pos hspecial]
      have howncast : (ownBonus G i : ℝ) = 5/2 := by rw [hownval]; norm_num
      have hnextcast : (nextBonus G i : ℝ) = 5/2 := by rw [hnextval]; norm_num
      linarith only [hown, howncast, hnext, hnextcast, hboundary]
    · have hp (v : Fin G.n) : ¬ (i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) := by
        rintro (h | h)
        · exact hspecial ⟨v, h⟩
        · exact hfollowing ⟨v, h⟩
      have hboundary0 : (List.finRange G.n).filter
          (fun v => i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro v _
        simpa using hp v
      rw [hboundary0]
      simp only [List.map_nil, List.sum_nil, add_zero]
      have hownval : (ownBonus G i : ℝ) ≤ 3 := by exact_mod_cast (ownBonus_bounds G i).2
      have hnextval : (nextBonus G i : ℝ) ≤ 3 := by exact_mod_cast (nextBonus_bounds G i).2
      linarith

theorem N_pos (G : HZTractability.ThrGraph) : 0 < N G := by
  unfold N
  positivity

theorem eta_lt_one (G : HZTractability.ThrGraph) : eta G < 1 := by
  have hN : (1 : ℝ) ≤ N G := by exact_mod_cast N_pos G
  unfold eta
  apply (div_lt_one (by positivity : 0 < 100 * (N G : ℝ)^2)).mpr
  nlinarith

theorem sum_lengths {n : ℕ} (T : Allocation ℝ n) :
    ∑ j, T.length j = T.cuts (Fin.last n) - T.cuts 0 := by
  unfold Allocation.length
  rw [Finset.sum_sub_distrib]
  have hleft := Fin.sum_univ_succ T.cuts
  have hright := Fin.sum_univ_castSucc T.cuts
  linarith

theorem piece_length_bounds (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (j : Fin (N G)) :
    (B G : ℝ) - 7 < T.length j ∧ T.length j < (B G : ℝ) + 7 := by
  have hN : 0 < (N G : ℝ) := by exact_mod_cast N_pos G
  have hsum : ∑ r, T.length r = (N G : ℝ) * (B G : ℝ) := by
    have hend : T.cuts (Fin.last (N G)) = (L G : ℝ) := hT.1.2.1
    rw [sum_lengths, hT.1.1, hend]
    simp only [L, Nat.cast_mul, sub_zero]
  have hpair (r s : Fin (N G)) : T.length s ≤ T.length r + (6 + eta G) := by
    let i := T.assign.symm r
    have hi : T.assign i = r := T.assign.apply_symm_apply r
    have henv := hT.2 i s
    rw [hi] at henv
    have hbr := bonus_bound G i (T.cuts r.castSucc) (T.cuts r.succ)
    have hbs := bonus_bound G i (T.cuts s.castSucc) (T.cuts s.succ)
    unfold Allocation.length
    linarith
  have hu : (N G : ℝ) * T.length j ≤
      (N G : ℝ) * B G + (N G : ℝ) * (6 + eta G) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hpair r j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_add_distrib, hsum] using h
  have hl : (N G : ℝ) * B G ≤
      (N G : ℝ) * T.length j + (N G : ℝ) * (6 + eta G) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hpair j r)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_add_distrib, hsum, mul_add] using h
  have he := eta_lt_one G
  have hupper : T.length j ≤ (B G : ℝ) + (6 + eta G) := by nlinarith
  have hlower : (B G : ℝ) - (6 + eta G) ≤ T.length j := by nlinarith
  constructor <;> linarith

theorem cut_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    ∀ j : Fin (N G + 1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G := by
  have hstep (j : Fin (N G)) : |T.length j - (B G : ℝ)| < 7 := by
    obtain ⟨hl, hu⟩ := piece_length_bounds G T hT j
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hprefix : ∀ j : Fin (N G + 1),
      |T.cuts j - (j.val : ℝ) * B G| ≤ 7 * j.val ∧
      (0 < j.val → |T.cuts j - (j.val : ℝ) * B G| < 7 * j.val) := by
    apply Fin.induction
    · simp [hT.1.1]
    · intro j ih
      have heq : T.cuts j.succ - (j.succ.val : ℝ) * B G =
          (T.cuts j.castSucc - (j.val : ℝ) * B G) + (T.length j - B G) := by
        simp only [Allocation.length, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring
      have hlt : |T.cuts j.succ - (j.succ.val : ℝ) * B G| < 7 * j.succ.val := by
        rw [heq]
        calc
          _ ≤ |T.cuts j.castSucc - (j.val : ℝ) * B G| + |T.length j - B G| :=
            abs_add_le _ _
          _ < 7 * (j.val : ℝ) + 7 := add_lt_add_of_le_of_lt ih.1 (hstep j)
          _ = 7 * (j.succ.val : ℝ) := by
            simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
            ring
      exact ⟨hlt.le, fun _ => hlt⟩
  intro j
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    rw [hj0, hT.1.1]
    have hN : (0 : ℝ) < N G := by exact_mod_cast N_pos G
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero, abs_zero] using
      (mul_pos (by norm_num : (0 : ℝ) < 7) hN)
  · exact (hprefix j).2 (Nat.pos_of_ne_zero hj) |>.trans_le
      (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.le_of_lt_succ j.isLt : (j.val : ℝ) ≤ N G)
        (by norm_num))

theorem core_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) :
    ∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅ := by
  have hN : 0 < (N G : ℝ) := by exact_mod_cast N_pos G
  have hB : 0 ≤ (B G : ℝ) := Nat.cast_nonneg _
  intro j
  have hjleft := abs_lt.mp (hcuts j.castSucc)
  have hjright := abs_lt.mp (hcuts j.succ)
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hjleft hjright
  constructor
  · intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    change T.cuts j.castSucc ≤ x ∧ x ≤ T.cuts j.succ
    change (j.val : ℝ) * B G + 10 * N G ≤ x at hxl
    change x ≤ ((j.val + 1 : ℕ) : ℝ) * B G - 10 * N G at hxr
    push_cast at hxr
    constructor <;> linarith
  · intro k hkj
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨⟨hxjl, hxjr⟩, hxkl, hxkr⟩ := hx
    change T.cuts j.castSucc ≤ x at hxjl
    change x ≤ T.cuts j.succ at hxjr
    change (k.val : ℝ) * B G + 10 * N G ≤ x at hxkl
    change x ≤ ((k.val + 1 : ℕ) : ℝ) * B G - 10 * N G at hxkr
    push_cast at hxkr
    have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hkidx : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
      have hmul := mul_le_mul_of_nonneg_right hkidx hB
      linarith
    · have hkidx : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast hgt
      have hmul := mul_le_mul_of_nonneg_right hkidx hB
      linarith

theorem overlap_unit (x b c : ℝ) (hx : x ≤ c) :
    overlap x b c (c+1) = clip (b-c) := by
  unfold overlap clip
  rw [max_eq_right hx]
  by_cases hbc : b ≤ c
  · rw [min_eq_left (by linarith : b ≤ c+1), max_eq_left (by linarith : b-c ≤ 0),
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  · by_cases hcb : c + 1 ≤ b
    · rw [min_eq_right hcb]
      have hdiff : c+1-c = 1 := by ring
      rw [hdiff, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by linarith : 0 ≤ b-c), min_eq_left (by linarith : 1 ≤ b-c)]
    · rw [min_eq_left (le_of_not_ge hcb), max_eq_right (by linarith : 0 ≤ b-c),
        min_eq_right (by linarith : b-c ≤ 1)]

theorem a_pos (G : HZTractability.ThrGraph) (v : Fin G.n) : 0 < a G v := by
  have hR := R_ge G
  unfold a
  positivity

theorem consecutive_special (G : HZTractability.ThrGraph) (v : Fin G.n) :
    (specialPiece G v).succ = (followingPiece G v).castSucc := by
  apply Fin.ext
  have ha := a_pos G v
  simp only [Fin.val_succ, Fin.val_castSucc, specialPiece, followingPiece]
  omega

theorem boundary_outer_bounds (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G)
    (v : Fin G.n) :
    T.cuts (specialPiece G v).castSucc ≤ ((boundary G v).1 : ℝ) ∧
      ((boundary G v).2 : ℝ) ≤ T.cuts (followingPiece G v).succ := by
  have hN : (1 : ℝ) ≤ N G := by exact_mod_cast N_pos G
  have hB : (B G : ℝ) = 40 * N G := by simp [B]
  have ha := a_pos G v
  have hspecial : ((specialPiece G v).val : ℝ) = (a G v : ℝ) - 1 := by
    have hnat : (specialPiece G v).val + 1 = a G v := by
      simp only [specialPiece]
      omega
    have hreal : ((specialPiece G v).val : ℝ) + 1 = (a G v : ℝ) := by exact_mod_cast hnat
    linarith
  have hleft := (abs_lt.mp (hcuts (specialPiece G v).castSucc)).2
  have hright := (abs_lt.mp (hcuts (followingPiece G v).succ)).1
  simp only [Fin.val_castSucc, hspecial] at hleft
  have hfollowing : (followingPiece G v).val = a G v := rfl
  simp only [Fin.val_succ, hfollowing, Nat.cast_add, Nat.cast_one] at hright
  simp only [boundary]
  push_cast
  constructor <;> nlinarith only [hleft, hright, hN, hB]

theorem boundary_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) :
    ∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v := by
  intro v
  have houter := boundary_outer_bounds G T hcuts v
  constructor
  · intro x hx
    change ((boundary G v).1 : ℝ) ≤ x ∧ x ≤ ((boundary G v).2 : ℝ) at hx
    by_cases hmid : x ≤ T.cuts (specialPiece G v).succ
    · exact Or.inl ⟨houter.1.trans hx.1, hmid⟩
    · apply Or.inr
      constructor
      · rw [← consecutive_special G v]
        exact le_of_not_ge hmid
      · exact hx.2.trans houter.2
  · have hlength : ((boundary G v).2 : ℝ) = ((boundary G v).1 : ℝ) + 1 := by
      simp only [boundary]
      push_cast
      ring
    rw [hlength, overlap_unit _ _ _ houter.1]
    unfold z
    congr 1
    simp only [boundary]
    push_cast
    ring

end ContiguousCake597.Approximate.LocalizationProof

namespace ContiguousCake597.Approximate

theorem lemma_6_proof (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) ∧
    (∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅) ∧
    (∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v) := by
  have hcuts := LocalizationProof.cut_localization G T hT
  exact ⟨hcuts, LocalizationProof.core_localization G T hcuts,
    LocalizationProof.boundary_localization G T hcuts⟩

end ContiguousCake597.Approximate


open ContiguousCake597.Approximate

theorem solution (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) ∧
    (∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅) ∧
    (∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v) := by
  exact ContiguousCake597.Approximate.lemma_6_proof G hn hdeg T hT

#print axioms solution
