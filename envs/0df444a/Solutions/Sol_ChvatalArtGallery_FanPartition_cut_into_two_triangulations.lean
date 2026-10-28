-- Prove2me | solution 1 for ChvatalArtGallery.FanPartition.cut_into_two_triangulations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:51:53.442131+00:00
-- url     : https://prove2.me/submissions/dc3c8965-1272-4693-a0c8-c5198123612e

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

private lemma cdist_eq {n : ℕ} (a b : Fin n) :
    cdist a b = if a.val ≤ b.val then b.val - a.val else b.val + n - a.val := by
  unfold cdist
  have ha := a.isLt
  have hb := b.isLt
  split_ifs with h
  · have h1 : b.val + n - a.val = (b.val - a.val) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma cdist_lt {n : ℕ} (a b : Fin n) : cdist a b < n := by
  have ha := a.isLt; have hb := b.isLt
  rw [cdist_eq]; split_ifs <;> omega

private lemma shift_val_eq {n : ℕ} (j : Fin n) (i : ℕ) (hi : i < n) :
    (shift j i).val = if j.val + i < n then j.val + i else j.val + i - n := by
  unfold shift
  have hj := j.isLt
  dsimp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have h1 : (j.val + i) % n = (j.val + i - n) % n := by
      conv_lhs => rw [show j.val + i = (j.val + i - n) + n by omega]
      exact Nat.add_mod_right _ _
    rw [h1]
    exact Nat.mod_eq_of_lt (by omega)

private lemma cdist_shift {n : ℕ} (j : Fin n) (i : ℕ) (hi : i < n) :
    cdist j (shift j i) = i := by
  have hj := j.isLt
  rw [cdist_eq, shift_val_eq j i hi]
  split_ifs <;> omega

private lemma shift_cdist {n : ℕ} (j x : Fin n) : shift j (cdist j x) = x := by
  ext
  have hj := j.isLt; have hx := x.isLt
  rw [shift_val_eq j (cdist j x) (cdist_lt j x), cdist_eq]
  split_ifs <;> omega

private lemma shift_zero {n : ℕ} (j : Fin n) : shift j 0 = j := by
  ext
  have hj := j.isLt
  rw [shift_val_eq j 0 (by omega)]
  split_ifs <;> omega

private lemma shift_shift_sub {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2) :
    shift (shift j k) (n - k) = j := by
  ext
  have hj := j.isLt
  rw [shift_val_eq (shift j k) (n - k) (by omega), shift_val_eq j k (by omega)]
  split_ifs <;> omega

private lemma cdist_eq_of_cdist {n : ℕ} (j x y : Fin n) :
    cdist x y =
      if cdist j x ≤ cdist j y then cdist j y - cdist j x else cdist j y + n - cdist j x := by
  have hj := j.isLt; have hx := x.isLt; have hy := y.isLt
  simp only [cdist_eq]
  (repeat split_ifs) <;> omega

private lemma cdist_arc {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (a : Fin (k + 1)) :
    cdist j (arc j (k + 1) a) = a.val := by
  unfold arc
  have ha := a.isLt
  exact cdist_shift j a.val (by omega)

private lemma arc_injective {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2) :
    Function.Injective (arc j (k + 1)) := by
  intro a b hab
  ext
  rw [← cdist_arc j k hk2 hkn a, ← cdist_arc j k hk2 hkn b, hab]

private lemma cdist_arc_eq {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (a b : Fin (k + 1)) :
    cdist (arc j (k + 1) a) (arc j (k + 1) b) =
      if a.val ≤ b.val then b.val - a.val else b.val + n - a.val := by
  rw [cdist_eq_of_cdist j, cdist_arc j k hk2 hkn a, cdist_arc j k hk2 hkn b]

private lemma isDiagonal_pair_iff {m : ℕ} (a b : Fin m) :
    IsDiagonal s(a, b) ↔ a ≠ b ∧ cdist a b ≠ 1 ∧ cdist b a ≠ 1 := by
  constructor
  · intro h
    exact h a b rfl
  · rintro ⟨hab, h1, h2⟩ x y hxy
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hab, h1, h2⟩
    · exact ⟨hab.symm, h2, h1⟩

private lemma isBoundaryEdge_pair_iff {m : ℕ} (a b : Fin m) :
    IsBoundaryEdge s(a, b) ↔ cdist a b = 1 ∨ cdist b a = 1 := by
  constructor
  · rintro ⟨x, y, hxy, hcd⟩
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hcd
    · exact Or.inr hcd
  · rintro (h | h)
    · exact ⟨a, b, rfl, h⟩
    · exact ⟨b, a, Sym2.eq_swap, h⟩

private lemma isDiagonal_arc_iff {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (a b : Fin (k + 1)) :
    IsDiagonal s(a, b) ↔
      IsDiagonal s(arc j (k + 1) a, arc j (k + 1) b) ∧
        ¬ (a.val = 0 ∧ b.val = k) ∧ ¬ (a.val = k ∧ b.val = 0) := by
  rw [isDiagonal_pair_iff, isDiagonal_pair_iff]
  have ha := a.isLt; have hb := b.isLt
  have hinj : arc j (k + 1) a ≠ arc j (k + 1) b ↔ a ≠ b :=
    (arc_injective j k hk2 hkn).ne_iff
  rw [hinj, Fin.ne_iff_vne, cdist_eq a b, cdist_eq b a,
    cdist_arc_eq j k hk2 hkn a b, cdist_arc_eq j k hk2 hkn b a]
  split_ifs <;> omega

private lemma cdist_arc_pos_iff {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (a b : Fin (k + 1)) :
    0 < cdist a b ↔ 0 < cdist (arc j (k + 1) a) (arc j (k + 1) b) := by
  have ha := a.isLt; have hb := b.isLt
  rw [cdist_eq a b, cdist_arc_eq j k hk2 hkn a b]
  split_ifs <;> omega

private lemma cdist_arc_lt_iff {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (a b c : Fin (k + 1)) :
    cdist a b < cdist a c ↔
      cdist (arc j (k + 1) a) (arc j (k + 1) b) < cdist (arc j (k + 1) a) (arc j (k + 1) c) := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  rw [cdist_eq a b, cdist_eq a c, cdist_arc_eq j k hk2 hkn a b, cdist_arc_eq j k hk2 hkn a c]
  (repeat split_ifs) <;> omega

private lemma crosses_map_arc_iff {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (e f : Sym2 (Fin (k + 1))) :
    Crosses e f ↔ Crosses (Sym2.map (arc j (k + 1)) e) (Sym2.map (arc j (k + 1)) f) := by
  induction e using Sym2.ind with | _ e1 e2 =>
  induction f using Sym2.ind with | _ f1 f2 =>
  simp only [Sym2.map_mk]
  constructor
  · rintro ⟨a, b, c, d, hab, hcd, h1, h2, h3⟩
    refine ⟨arc j (k + 1) a, arc j (k + 1) b, arc j (k + 1) c, arc j (k + 1) d, ?_, ?_,
      (cdist_arc_pos_iff j k hk2 hkn a c).mp h1,
      (cdist_arc_lt_iff j k hk2 hkn a c b).mp h2,
      (cdist_arc_lt_iff j k hk2 hkn a b d).mp h3⟩
    · exact congrArg (Sym2.map (arc j (k + 1))) hab
    · exact congrArg (Sym2.map (arc j (k + 1))) hcd
  · rintro ⟨a', b', c', d', hab, hcd, h1, h2, h3⟩
    rw [Sym2.eq_iff] at hab hcd
    have hex_ab : ∃ a b : Fin (k + 1), s(e1, e2) = s(a, b) ∧
        a' = arc j (k + 1) a ∧ b' = arc j (k + 1) b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e1, e2, rfl, rfl, rfl⟩
      · exact ⟨e2, e1, Sym2.eq_swap, rfl, rfl⟩
    have hex_cd : ∃ c d : Fin (k + 1), s(f1, f2) = s(c, d) ∧
        c' = arc j (k + 1) c ∧ d' = arc j (k + 1) d := by
      rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨f1, f2, rfl, rfl, rfl⟩
      · exact ⟨f2, f1, Sym2.eq_swap, rfl, rfl⟩
    rcases hex_ab with ⟨a, b, hab_eq, rfl, rfl⟩
    rcases hex_cd with ⟨c, d, hcd_eq, rfl, rfl⟩
    exact ⟨a, b, c, d, hab_eq, hcd_eq,
      (cdist_arc_pos_iff j k hk2 hkn a c).mpr h1,
      (cdist_arc_lt_iff j k hk2 hkn a c b).mpr h2,
      (cdist_arc_lt_iff j k hk2 hkn a b d).mpr h3⟩

private lemma chord_endpoints_le_k {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (x y u v : Fin n)
    (hx : cdist j x ≤ k) (hy : cdist j y ≤ k)
    (h1 : 0 < cdist x u) (h2 : cdist x u < cdist x y) (h3 : cdist x y < cdist x v)
    (hnc : ¬ Crosses s(j, shift j k) s(u, v)) :
    cdist j u ≤ k ∧ cdist j v ≤ k ∧
      ¬ (cdist j u = 0 ∧ cdist j v = k) ∧ ¬ (cdist j v = 0 ∧ cdist j u = k) := by
  have hjk_cdist : cdist j (shift j k) = k := cdist_shift j k (by omega)
  have hnu : ¬ (0 < cdist j u ∧ cdist j u < k ∧ k < cdist j v) := by
    rintro ⟨hu1, hu2, hv⟩
    exact hnc ⟨j, shift j k, u, v, rfl, rfl, hu1, hjk_cdist.symm ▸ hu2, hjk_cdist.symm ▸ hv⟩
  have hnv : ¬ (0 < cdist j v ∧ cdist j v < k ∧ k < cdist j u) := by
    rintro ⟨hv1, hv2, hu⟩
    exact hnc ⟨j, shift j k, v, u, rfl, Sym2.eq_swap, hv1, hjk_cdist.symm ▸ hv2, hjk_cdist.symm ▸ hu⟩
  have hlu := cdist_lt j u; have hlv := cdist_lt j v
  rw [cdist_eq_of_cdist j x u] at h1 h2
  rw [cdist_eq_of_cdist j x y] at h2 h3
  rw [cdist_eq_of_cdist j x v] at h3
  (repeat split_ifs at h1 h2 h3) <;> omega

private lemma isTriangulation_pullback_arc {n : ℕ} (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, shift j k) ∈ D) :
    IsTriangulation (k + 1) (pullback (arc j (k + 1)) D) := by
  rcases hD with ⟨_, hD_diag, hD_nc, hD_max⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · intro e he f hf hcross
    have heD := (Finset.mem_filter.mp he).2.2
    have hfD := (Finset.mem_filter.mp hf).2.2
    exact hD_nc _ heD _ hfD ((crosses_map_arc_iff j k hk2 hkn e f).mp hcross)
  · intro e he_diag he_nc
    simp only [pullback, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨he_diag, ?_⟩
    induction e using Sym2.ind with | _ a b =>
    have he_diag_n : IsDiagonal (Sym2.map (arc j (k + 1)) s(a, b)) :=
      ((isDiagonal_arc_iff j k hk2 hkn a b).mp he_diag).1
    apply hD_max _ he_diag_n
    intro g hgD hcross
    rcases hcross with ⟨x, y, u, v, hxy, huv, h1, h2, h3⟩
    subst huv
    simp only [Sym2.map_mk] at hxy
    have hxy_le : cdist j x ≤ k ∧ cdist j y ≤ k := by
      rw [Sym2.eq_iff] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by rw [cdist_arc j k hk2 hkn]; omega, by rw [cdist_arc j k hk2 hkn]; omega⟩
      · exact ⟨by rw [cdist_arc j k hk2 hkn]; omega, by rw [cdist_arc j k hk2 hkn]; omega⟩
    have hnc_jk : ¬ Crosses s(j, shift j k) s(u, v) := hD_nc _ hjk _ hgD
    obtain ⟨hu_le, hv_le, hnuv0k, hnv0uk⟩ :=
      chord_endpoints_le_k j k hk2 hkn x y u v hxy_le.1 hxy_le.2 h1 h2 h3 hnc_jk
    let c : Fin (k + 1) := ⟨cdist j u, by omega⟩
    let d : Fin (k + 1) := ⟨cdist j v, by omega⟩
    have hc_eq : arc j (k + 1) c = u := shift_cdist j u
    have hd_eq : arc j (k + 1) d = v := shift_cdist j v
    have hmap_cd : Sym2.map (arc j (k + 1)) s(c, d) = s(u, v) := by
      simp only [Sym2.map_mk, hc_eq, hd_eq]
    have hcd_diag : IsDiagonal s(c, d) := by
      rw [isDiagonal_arc_iff j k hk2 hkn c d, hc_eq, hd_eq]
      exact ⟨hD_diag s(u, v) hgD, hnuv0k, fun h => hnv0uk ⟨h.2, h.1⟩⟩
    have hcd_mem : s(c, d) ∈ pullback (arc j (k + 1)) D := by
      simp only [pullback, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcd_diag, hmap_cd.symm ▸ hgD⟩
    have hcross_n : Crosses (Sym2.map (arc j (k + 1)) s(a, b)) (Sym2.map (arc j (k + 1)) s(c, d)) :=
      ⟨x, y, u, v, hxy, hmap_cd, h1, h2, h3⟩
    exact he_nc s(c, d) hcd_mem ((crosses_map_arc_iff j k hk2 hkn s(a, b) s(c, d)).mpr hcross_n)

private lemma isEdge_pullback_arc_iff {n : ℕ} (D : Finset (Sym2 (Fin n)))
    (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, shift j k) ∈ D) (a b : Fin (k + 1)) (hab : a ≠ b) :
    IsEdge (pullback (arc j (k + 1)) D) s(a, b) ↔
      IsEdge D s(arc j (k + 1) a, arc j (k + 1) b) := by
  have ha := a.isLt; have hb := b.isLt
  constructor
  · rintro (hbd | hmem)
    · rw [isBoundaryEdge_pair_iff, cdist_eq a b, cdist_eq b a] at hbd
      have hcases : (b.val = a.val + 1 ∨ a.val = b.val + 1) ∨
          (a.val = 0 ∧ b.val = k) ∨ (a.val = k ∧ b.val = 0) := by
        split_ifs at hbd <;> omega
      rcases hcases with hstep | ⟨ha0, hbk⟩ | ⟨hak, hb0⟩
      · left
        rw [isBoundaryEdge_pair_iff, cdist_arc_eq j k hk2 hkn a b, cdist_arc_eq j k hk2 hkn b a]
        split_ifs <;> omega
      · right
        have ha_eq : arc j (k + 1) a = j := by unfold arc; rw [ha0, shift_zero]
        have hb_eq : arc j (k + 1) b = shift j k := by unfold arc; rw [hbk]
        rw [ha_eq, hb_eq]
        exact hjk
      · right
        have ha_eq : arc j (k + 1) a = shift j k := by unfold arc; rw [hak]
        have hb_eq : arc j (k + 1) b = j := by unfold arc; rw [hb0, shift_zero]
        rw [ha_eq, hb_eq, Sym2.eq_swap]
        exact hjk
    · right
      exact (Finset.mem_filter.mp hmem).2.2
  · intro hedge
    by_cases hbd : IsBoundaryEdge s(a, b)
    · exact Or.inl hbd
    · right
      have hdiag : IsDiagonal s(a, b) := by
        rw [isDiagonal_pair_iff]
        rw [isBoundaryEdge_pair_iff, not_or] at hbd
        exact ⟨hab, hbd.1, hbd.2⟩
      have hdiag_n : IsDiagonal s(arc j (k + 1) a, arc j (k + 1) b) :=
        ((isDiagonal_arc_iff j k hk2 hkn a b).mp hdiag).1
      rcases hedge with hbd_n | hmem_D
      · rw [isBoundaryEdge_pair_iff] at hbd_n
        rw [isDiagonal_pair_iff] at hdiag_n
        rcases hbd_n with h1 | h2
        · exact (hdiag_n.2.1 h1).elim
        · exact (hdiag_n.2.2 h2).elim
      · simp only [pullback, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hdiag, hmem_D⟩

private lemma mem_image_triangles_pullback_arc_iff {n : ℕ} (D : Finset (Sym2 (Fin n)))
    (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, shift j k) ∈ D) (T' : Finset (Fin n)) :
    T' ∈ (triangles (k + 1) (pullback (arc j (k + 1)) D)).image
        (fun T => T.image (arc j (k + 1))) ↔
      T' ∈ triangles n D ∧ ∀ v ∈ T', cdist j v ≤ k := by
  have hinj := arc_injective j k hk2 hkn
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and] at hT ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective T hinj, hT.1]
    · intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun h => hxy (congrArg _ h)
      exact (isEdge_pullback_arc_iff D j k hk2 hkn hjk a b hab).mp (hT.2 a ha b hb hab)
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨a, _, rfl⟩
      rw [cdist_arc j k hk2 hkn a]
      omega
  · rintro ⟨hT', hv_le⟩
    simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and] at hT'
    let T : Finset (Fin (k + 1)) := Finset.univ.filter (fun a => arc j (k + 1) a ∈ T')
    have hT_image : T.image (arc j (k + 1)) = T' := by
      ext v
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hv
        refine ⟨⟨cdist j v, by have := hv_le v hv; omega⟩, ?_, shift_cdist j v⟩
        rw [show arc j (k + 1) ⟨cdist j v, _⟩ = v from shift_cdist j v]
        exact hv
    refine ⟨T, ?_, hT_image⟩
    simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    refine ⟨?_, ?_⟩
    · have hcard := Finset.card_image_of_injective T hinj
      rw [hT_image, hT'.1] at hcard
      exact hcard.symm
    · intro a ha b hb hab
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [isEdge_pullback_arc_iff D j k hk2 hkn hjk a b hab]
      exact hT'.2 _ ha _ hb (hinj.ne hab)

private lemma cdist_shift_le_sub_iff {n : ℕ} (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (v : Fin n) :
    cdist (shift j k) v ≤ n - k ↔ cdist j v = 0 ∨ k ≤ cdist j v := by
  have hlv := cdist_lt j v
  rw [cdist_eq_of_cdist j (shift j k) v, cdist_shift j k (by omega)]
  split_ifs <;> omega

/-- Proof of the Theorem, p. 40: an inner edge (j, j + k) cuts an n-triangulation into a
(k + 1)-triangulation G₁ on the vertices j, …, j + k and an (n − k + 1)-triangulation G₂ on the
vertices j + k, …, j + n = j, whose triangles together are exactly the triangles of G, with no
triangle in both. -/
theorem cut_into_two_triangulations (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) (j : Fin n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, shift j k) ∈ D) :
    let ι₁ : Fin (k + 1) → Fin n := arc j (k + 1)
    let ι₂ : Fin (n - k + 1) → Fin n := arc (shift j k) (n - k + 1)
    let D₁ := pullback ι₁ D
    let D₂ := pullback ι₂ D
    IsTriangulation (k + 1) D₁ ∧ IsTriangulation (n - k + 1) D₂ ∧
      Disjoint ((triangles (k + 1) D₁).image (fun T => T.image ι₁))
        ((triangles (n - k + 1) D₂).image (fun T => T.image ι₂)) ∧
      (triangles (k + 1) D₁).image (fun T => T.image ι₁) ∪
        (triangles (n - k + 1) D₂).image (fun T => T.image ι₂) = triangles n D := by
  intro ι₁ ι₂ D₁ D₂
  have hnk2 : 2 ≤ n - k := by omega
  have hnkn : n - k ≤ n - 2 := by omega
  have hjk' : s(shift j k, shift (shift j k) (n - k)) ∈ D := by
    rw [shift_shift_sub j k hk2 hkn, Sym2.eq_swap]
    exact hjk
  have htri1 : IsTriangulation (k + 1) D₁ :=
    isTriangulation_pullback_arc D hD j k hk2 hkn hjk
  have htri2 : IsTriangulation (n - k + 1) D₂ :=
    isTriangulation_pullback_arc D hD (shift j k) (n - k) hnk2 hnkn hjk'
  have himg1 : ∀ T', T' ∈ (triangles (k + 1) D₁).image (fun T => T.image ι₁) ↔
      T' ∈ triangles n D ∧ ∀ v ∈ T', cdist j v ≤ k :=
    mem_image_triangles_pullback_arc_iff D j k hk2 hkn hjk
  have himg2 : ∀ T', T' ∈ (triangles (n - k + 1) D₂).image (fun T => T.image ι₂) ↔
      T' ∈ triangles n D ∧ ∀ v ∈ T', cdist j v = 0 ∨ k ≤ cdist j v := by
    intro T'
    rw [mem_image_triangles_pullback_arc_iff D (shift j k) (n - k) hnk2 hnkn hjk']
    simp only [cdist_shift_le_sub_iff j k hk2 hkn]
  refine ⟨htri1, htri2, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro T' h1 h2
    rw [himg1] at h1
    rw [himg2] at h2
    have hsub : T' ⊆ ({j, shift j k} : Finset (Fin n)) := by
      intro v hv
      have hv1 := h1.2 v hv
      have hv2 := h2.2 v hv
      have h0k : cdist j v = 0 ∨ cdist j v = k := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h0k with h0 | hk
      · left
        rw [← shift_cdist j v, h0, shift_zero]
      · right
        rw [← shift_cdist j v, hk]
    have hcard_le : T'.card ≤ ({j, shift j k} : Finset (Fin n)).card :=
      Finset.card_le_card hsub
    have hcard_pair : ({j, shift j k} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hcard_T' : T'.card = 3 := by
      have hT' := h1.1
      simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard] at hT'
      exact hT'.1.2
    omega
  · ext T'
    rw [Finset.mem_union, himg1, himg2]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hT'
      by_contra hnot
      push Not at hnot
      rcases hnot with ⟨hnot1, hnot2⟩
      obtain ⟨u, huT', hu_gt⟩ := hnot1 hT'
      obtain ⟨w, hwT', hw_lt⟩ := hnot2 hT'
      have hlu := cdist_lt j u
      have hlw := cdist_lt j w
      have hw_range : 0 < cdist j w ∧ cdist j w < k := by omega
      have hu_range : k < cdist j u := by omega
      have hwu_ne : w ≠ u := by
        intro heq
        subst heq
        omega
      have hT'_edges := hT'
      simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard] at hT'_edges
      have hedge_wu : IsEdge D s(w, u) := hT'_edges.2 w hwT' u huT' hwu_ne
      have hnot_bd : ¬ IsBoundaryEdge s(w, u) := by
        rw [isBoundaryEdge_pair_iff, cdist_eq_of_cdist j w u, cdist_eq_of_cdist j u w]
        split_ifs <;> omega
      have hwu_D : s(w, u) ∈ D := hedge_wu.resolve_left hnot_bd
      have hcross : Crosses s(j, shift j k) s(w, u) := by
        refine ⟨j, shift j k, w, u, rfl, rfl, hw_range.1, ?_, ?_⟩
        · rw [cdist_shift j k (by omega)]; exact hw_range.2
        · rw [cdist_shift j k (by omega)]; exact hu_range
      exact hD.2.2.1 _ hjk _ hwu_D hcross

end ChvatalArtGallery.FanPartition

theorem solution (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (hD : ChvatalArtGallery.FanPartition.IsTriangulation n D) (j : Fin n) (k : ℕ)
    (hk2 : 2 ≤ k) (hkn : k ≤ n - 2)
    (hjk : s(j, ChvatalArtGallery.FanPartition.shift j k) ∈ D) :
    let ι₁ : Fin (k + 1) → Fin n := ChvatalArtGallery.FanPartition.arc j (k + 1)
    let ι₂ : Fin (n - k + 1) → Fin n :=
      ChvatalArtGallery.FanPartition.arc (ChvatalArtGallery.FanPartition.shift j k) (n - k + 1)
    let D₁ := ChvatalArtGallery.FanPartition.pullback ι₁ D
    let D₂ := ChvatalArtGallery.FanPartition.pullback ι₂ D
    ChvatalArtGallery.FanPartition.IsTriangulation (k + 1) D₁ ∧
      ChvatalArtGallery.FanPartition.IsTriangulation (n - k + 1) D₂ ∧
      Disjoint ((ChvatalArtGallery.FanPartition.triangles (k + 1) D₁).image (fun T => T.image ι₁))
        ((ChvatalArtGallery.FanPartition.triangles (n - k + 1) D₂).image (fun T => T.image ι₂)) ∧
      (ChvatalArtGallery.FanPartition.triangles (k + 1) D₁).image (fun T => T.image ι₁) ∪
        (ChvatalArtGallery.FanPartition.triangles (n - k + 1) D₂).image (fun T => T.image ι₂) =
        ChvatalArtGallery.FanPartition.triangles n D :=
  ChvatalArtGallery.FanPartition.cut_into_two_triangulations n D hD j k hk2 hkn hjk
