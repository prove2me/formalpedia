-- Prove2me | solution 1 for DetANN.HPIM.tree_points
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T07:50:20.39517+00:00
-- url     : https://prove2.me/submissions/4b027faf-4e73-4aaa-a092-fc22d6695c1f

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Theorems.Thm_DetANN_HPIM_median_threshold

/-! `tree_points`: the total number of points over the HPIM tree is at most `N (4 ⌈log₂ N⌉ + 1)`.

Potential `G x = x (4 ⌈log₂ x⌉ + 1)`. The induction step is a sum of a pointwise inequality over the
points, grouped by the components at threshold `2 r_med` (each class pays for itself). -/

namespace DetANN.HPIM.TP

open DetANN.HPIM Classical

/-! ### Arithmetic of `clog` -/

lemma clog_half {k n : ℕ} (hk : 1 ≤ k) (h : 2 * k ≤ n) : Nat.clog 2 k + 1 ≤ Nat.clog 2 n := by
  have hn : 2 ≤ n := by omega
  set c := Nat.clog 2 n with hcdef
  have hc : 1 ≤ c := Nat.clog_pos (by norm_num) hn
  have h1 : n ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : k ≤ 2 ^ (c - 1) := by omega
  have := Nat.clog_le_of_le_pow h3
  omega

lemma clog_reps {r n : ℕ} (hn : 2 ≤ n) (hr : r ≤ (n + 1) / 2) : Nat.clog 2 r + 1 ≤ Nat.clog 2 n := by
  set c := Nat.clog 2 n with hcdef
  have hc : 1 ≤ c := Nat.clog_pos (by norm_num) hn
  have h1 : n ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) n
  have h2 : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : r ≤ 2 ^ (c - 1) := by omega
  have := Nat.clog_le_of_le_pow h3
  omega

lemma four_e (e : ℕ) : 4 * e + 2 ≤ 3 * 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num
    · omega

lemma four_clog (s : ℕ) (hs : 1 ≤ s) : 4 * Nat.clog 2 s + 1 ≤ 3 * s := by
  rcases Nat.lt_or_ge s 2 with h | h
  · have : s = 1 := by omega
    subst this; simp
  · set c := Nat.clog 2 s with hcdef
    have hc : 1 ≤ c := Nat.clog_pos (by norm_num) h
    have hlt : 2 ^ (c - 1) < s := by
      have := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (show 1 < s by omega)
      rwa [Nat.pred_eq_sub_one] at this
    have := four_e (c - 1)
    omega

/-- The pointwise inequality: a point in a bottom class of size `k` inside a coarse class of size
`s`, with `r` coarse classes in all. -/
lemma pointwise (n r s k : ℕ) (hk1 : 1 ≤ k) (hks : k ≤ s) (hkn : 2 * k ≤ n) (hr : r ≤ (n + 1) / 2)
    (hcase : r ≤ s ∨ 2 * s + 1 ≤ n) :
    s + 4 * Nat.clog 2 r + 1 ≤ 4 * s * (Nat.clog 2 n - Nat.clog 2 k) := by
  have hn : 2 ≤ n := by omega
  have hkc := clog_half hk1 hkn
  have h1 := four_clog s (by omega)
  rcases hcase with h | h
  · have h2 : Nat.clog 2 r ≤ Nat.clog 2 s := Nat.clog_mono_right 2 h
    have h4 : 4 * s ≤ 4 * s * (Nat.clog 2 n - Nat.clog 2 k) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have h2 := clog_reps hn hr
    have hsc := clog_half (show 1 ≤ s by omega) (show 2 * s ≤ n by omega)
    have h5 : Nat.clog 2 k ≤ Nat.clog 2 s := Nat.clog_mono_right 2 hks
    set Δ := Nat.clog 2 n - Nat.clog 2 s with hΔ
    have h6 : 4 * s * Δ ≤ 4 * s * (Nat.clog 2 n - Nat.clog 2 k) := Nat.mul_le_mul_left _ (by omega)
    have h7 : 4 * (s - 1) ≤ 4 * (s - 1) * Δ := Nat.le_mul_of_pos_right _ (by omega)
    have e : 4 * s * Δ = 4 * Δ + 4 * (s - 1) * Δ := by
      have : s = (s - 1) + 1 := by omega
      conv_lhs => rw [this]
      ring
    omega

/-! ### Threshold classes -/

section Reach

variable {m n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m))

lemma reach_refl (d : ℝ) (i : Fin n) : thrReach P d i i := SimpleGraph.Reachable.refl _

lemma reach_symm {d : ℝ} {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h

lemma reach_trans {d : ℝ} {i j k : Fin n} (h1 : thrReach P d i j) (h2 : thrReach P d j k) :
    thrReach P d i k := SimpleGraph.Reachable.trans h1 h2

lemma reach_mono {d d' : ℝ} (hd : d ≤ d') {i j : Fin n} (h : thrReach P d i j) : thrReach P d' i j := by
  unfold thrReach at *
  refine SimpleGraph.Reachable.mono ?_ h
  intro a b hab
  rw [SimpleGraph.fromRel_adj] at hab ⊢
  exact ⟨hab.1, hab.2.imp (fun h => h.trans hd) (fun h => h.trans hd)⟩

/-- The class of `i` at threshold `d`. -/
noncomputable def cls (d : ℝ) (i : Fin n) : Finset (Fin n) := Finset.univ.filter (thrReach P d i)

lemma mem_cls {d : ℝ} {i j : Fin n} : j ∈ cls P d i ↔ thrReach P d i j := by
  simp [cls]

lemma cls_eq_iff {d : ℝ} {i j : Fin n} : cls P d i = cls P d j ↔ thrReach P d i j := by
  constructor
  · intro h
    have : j ∈ cls P d i := by rw [h]; exact (mem_cls P).2 (reach_refl P d j)
    exact (mem_cls P).1 this
  · intro h; ext x
    rw [mem_cls, mem_cls]
    exact ⟨fun hx => reach_trans P (reach_symm P h) hx, fun hx => reach_trans P h hx⟩

lemma fiber_cls (d : ℝ) (j : Fin n) :
    Finset.univ.filter (fun i => cls P d i = cls P d j) = cls P d j := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [cls_eq_iff, mem_cls]
  exact ⟨fun h => reach_symm P h, fun h => reach_symm P h⟩

/-- Each class contributes its size to a sum over the points of the class-wise data. -/
lemma sum_classes (d : ℝ) (w : Fin n → ℕ) :
    ∑ A ∈ Finset.univ.image (cls P d), ∑ i ∈ Finset.univ.filter (fun i => cls P d i = A), w i =
      ∑ i, w i :=
  Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i)) w

/-- The number of classes is the number of representatives. -/
lemma card_classes (d : ℝ) (hrep : ∀ i : Fin n, ∃ j, thrReach P d i j ∧ IsRep P d j) :
    (Finset.univ.image (cls P d)).card = (Finset.univ.filter (IsRep P d)).card := by
  have himg : Finset.univ.image (cls P d) = (Finset.univ.filter (IsRep P d)).image (cls P d) := by
    ext A
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hij, hj⟩ := hrep i
      exact ⟨j, hj, ((cls_eq_iff P).2 hij).symm⟩
    · rintro ⟨j, -, rfl⟩; exact ⟨j, rfl⟩
  rw [himg, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
  have h := (cls_eq_iff P).1 hab
  exact le_antisymm (ha b (reach_symm P h)) (hb a h)

end Reach

/-! ### The induction -/

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

/-- The potential. -/
def G (x : ℕ) : ℕ := x * (4 * Nat.clog 2 x + 1)

lemma le_G (x : ℕ) : x ≤ G x := by unfold G; exact Nat.le_mul_of_pos_right _ (by omega)

lemma compBotOf_card (S : Finset (Fin N)) (i : Fin S.card) :
    (compBotOf Y S i).card = (cls (ptsOf Y S) (2 * (rmedOf Y S / 2)) i).card := by
  unfold compBotOf cls; rw [Finset.card_map]

lemma compBotOf_eq_iff (S : Finset (Fin N)) (i j : Fin S.card) :
    compBotOf Y S i = compBotOf Y S j ↔
      cls (ptsOf Y S) (2 * (rmedOf Y S / 2)) i = cls (ptsOf Y S) (2 * (rmedOf Y S / 2)) j := by
  unfold compBotOf
  rw [Finset.map_inj]
  rfl

/-- The bottom classes, summed over the distinct components. -/
lemma sum_bottom (S : Finset (Fin N)) :
    ∑ C ∈ Finset.univ.image (compBotOf Y S), G C.card =
      ∑ i : Fin S.card, (4 * Nat.clog 2 (compBotOf Y S i).card + 1) := by
  set d := 2 * (rmedOf Y S / 2)
  rw [← Finset.sum_fiberwise_of_maps_to (g := compBotOf Y S) (t := Finset.univ.image (compBotOf Y S))
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  apply Finset.sum_congr rfl
  intro C hC
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hC
  have hf : Finset.univ.filter (fun i => compBotOf Y S i = compBotOf Y S j) =
      cls (ptsOf Y S) d j := by
    rw [← fiber_cls (ptsOf Y S) d j]
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact compBotOf_eq_iff Y S x j
  rw [Finset.sum_congr rfl (g := fun _ => 4 * Nat.clog 2 (compBotOf Y S j).card + 1)
    (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, hf, smul_eq_mul,
    ← compBotOf_card]
  rfl

lemma ptsOf_inj (hY : Function.Injective Y) (S : Finset (Fin N)) : Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

set_option maxHeartbeats 1000000 in
/-- **The induction step.** -/
lemma step (hY : Function.Injective Y) (f : ℕ) (IH : ∀ C : Finset (Fin N), treePts Y f C ≤ G C.card)
    (S : Finset (Fin N)) (hS : 2 ≤ S.card) : treePts Y (f + 1) S ≤ G S.card := by
  set n := S.card with hn
  set P := ptsOf Y S with hP
  set D := medThreshold P with hD
  have mt := median_threshold P
  obtain ⟨⟨i₀, hbig⟩, hDpos, hsmall⟩ := mt.2.2.2 hS (ptsOf_inj Y hY S)
  have hbig' : n / 2 + 1 ≤ (cls P D i₀).card := hbig
  have hd1 : 2 * (rmedOf Y S / 2) = D / 2 := by unfold rmedOf; ring
  have hd2 : 2 * rmedOf Y S = D := by unfold rmedOf; ring
  set d := 2 * (rmedOf Y S / 2) with hd
  have hdD : d ≤ D := by rw [hd1]; linarith
  have hdlt : d < D := by rw [hd1]; linarith
  -- the number of representatives
  set r := (repsOf Y S).card with hr
  have hrc : r = (Finset.univ.filter (IsRep P D)).card := by
    rw [hr]; unfold repsOf; rw [Finset.card_map, hd2]
  have hr2 : r ≤ (n + 1) / 2 := by rw [hrc]; exact mt.2.2.1 D i₀ hbig
  have hrcls : (Finset.univ.image (cls P D)).card = r := by
    rw [hrc]; exact card_classes P D (mt.2.1 D)
  -- the bottom class sizes
  set k : Fin n → ℕ := fun i => (compBotOf Y S i).card with hk
  have hk_cls : ∀ i, k i = (cls P d i).card := fun i => compBotOf_card Y S i
  have hk1 : ∀ i, 1 ≤ k i := fun i => by
    rw [hk_cls]; exact Finset.card_pos.2 ⟨i, (mem_cls P).2 (reach_refl P d i)⟩
  have hk2 : ∀ i, 2 * k i ≤ n := fun i => by
    rw [hk_cls]; have := hsmall d hdlt i; unfold cls; omega
  have hks : ∀ i, k i ≤ (cls P D i).card := fun i => by
    rw [hk_cls]; apply Finset.card_le_card
    intro x hx; exact (mem_cls P).2 (reach_mono P hdD ((mem_cls P).1 hx))
  -- the coarse cases
  have hcase : ∀ i, r ≤ (cls P D i).card ∨ 2 * (cls P D i).card + 1 ≤ n := by
    intro i
    by_cases h : cls P D i = cls P D i₀
    · left; rw [h]; omega
    · right
      have hdisj : Disjoint (cls P D i) (cls P D i₀) := by
        rw [Finset.disjoint_left]
        intro x hx hx0
        exact h ((cls_eq_iff P).2 (reach_trans P ((mem_cls P).1 hx)
          (reach_symm P ((mem_cls P).1 hx0))))
      have hu := Finset.card_union_of_disjoint hdisj
      have hle : (cls P D i ∪ cls P D i₀).card ≤ n := by
        have := Finset.card_le_univ (cls P D i ∪ cls P D i₀); simpa using this
      omega
  -- per point
  have hpt : ∀ i, (cls P D i).card + 4 * Nat.clog 2 r + 1 ≤
      4 * (cls P D i).card * (Nat.clog 2 n - Nat.clog 2 (k i)) :=
    fun i => pointwise n r _ _ (hk1 i) (hks i) (hk2 i) hr2 (hcase i)
  -- per coarse class
  have hclass : ∀ A ∈ Finset.univ.image (cls P D),
      A.card + 4 * Nat.clog 2 r + 1 ≤
        ∑ i ∈ Finset.univ.filter (fun i => cls P D i = A), 4 * (Nat.clog 2 n - Nat.clog 2 (k i)) := by
    intro A hA
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hA
    have hpos : 0 < (cls P D j).card := Finset.card_pos.2 ⟨j, (mem_cls P).2 (reach_refl P D j)⟩
    apply Nat.le_of_mul_le_mul_left _ hpos
    rw [Finset.mul_sum]
    calc (cls P D j).card * ((cls P D j).card + 4 * Nat.clog 2 r + 1)
        = ∑ i ∈ Finset.univ.filter (fun i => cls P D i = cls P D j),
            ((cls P D j).card + 4 * Nat.clog 2 r + 1) := by
          rw [Finset.sum_const, fiber_cls, smul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => cls P D i = cls P D j),
            (cls P D j).card * (4 * (Nat.clog 2 n - Nat.clog 2 (k i))) := by
          apply Finset.sum_le_sum
          intro i hi
          have := hpt i
          rw [(Finset.mem_filter.1 hi).2] at this
          calc _ ≤ 4 * (cls P D j).card * (Nat.clog 2 n - Nat.clog 2 (k i)) := this
            _ = _ := by ring
  -- sum over the classes
  have htot : n + r * (4 * Nat.clog 2 r + 1) ≤ ∑ i, 4 * (Nat.clog 2 n - Nat.clog 2 (k i)) := by
    rw [← sum_classes P D]
    have hsum := Finset.sum_le_sum hclass
    have e1 : ∑ A ∈ Finset.univ.image (cls P D), (A.card + 4 * Nat.clog 2 r + 1) =
        (∑ A ∈ Finset.univ.image (cls P D), A.card) + r * (4 * Nat.clog 2 r + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, hrcls,
        smul_eq_mul, smul_eq_mul]; ring
    have e2 : ∑ A ∈ Finset.univ.image (cls P D), A.card = n := by
      calc ∑ A ∈ Finset.univ.image (cls P D), A.card
          = ∑ A ∈ Finset.univ.image (cls P D),
              ∑ i ∈ Finset.univ.filter (fun i => cls P D i = A), (fun _ => 1) i := by
            apply Finset.sum_congr rfl
            intro A hA
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hA
            rw [fiber_cls, Finset.sum_const, smul_eq_mul, mul_one]
        _ = ∑ i : Fin n, (fun _ => 1) i := sum_classes P D _
        _ = n := by simp
    omega
  -- assemble
  have hunf : treePts Y (f + 1) S =
      n + (∑ C ∈ Finset.univ.image (compBotOf Y S), treePts Y f C) + treePts Y f (repsOf Y S) := by
    rw [treePts, if_neg (by omega)]
  rw [hunf]
  have h1 : ∑ C ∈ Finset.univ.image (compBotOf Y S), treePts Y f C ≤
      ∑ C ∈ Finset.univ.image (compBotOf Y S), G C.card := Finset.sum_le_sum (fun C _ => IH C)
  have h2 := IH (repsOf Y S)
  rw [sum_bottom] at h1
  have h3 : ∑ i : Fin n, (4 * Nat.clog 2 (k i) + 1) + ∑ i, 4 * (Nat.clog 2 n - Nat.clog 2 (k i)) =
      G n := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i : Fin n, 4 * Nat.clog 2 (k i) + 1 + 4 * (Nat.clog 2 n - Nat.clog 2 (k i)) =
        4 * Nat.clog 2 n + 1 := by
      intro i; have := clog_half (hk1 i) (hk2 i); omega
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    unfold G; ring
  unfold G at h2
  have h2' : treePts Y f (repsOf Y S) ≤ r * (4 * Nat.clog 2 r + 1) := h2
  have h1' : ∑ C ∈ Finset.univ.image (compBotOf Y S), treePts Y f C ≤
      ∑ i : Fin n, (4 * Nat.clog 2 (k i) + 1) := h1
  omega

theorem treePts_le_G (hY : Function.Injective Y) : ∀ f (S : Finset (Fin N)), treePts Y f S ≤ G S.card := by
  intro f
  induction f with
  | zero => intro S; rw [treePts]; exact le_G _
  | succ f ih =>
    intro S
    by_cases h : S.card ≤ 1
    · rw [treePts, if_pos h]; exact le_G _
    · exact step Y hY f ih S (by omega)

theorem tree_points' (hY : Function.Injective Y) :
    treePts Y (N + 1) Finset.univ ≤ 4 * N * (Nat.clog 2 N + 1) := by
  have h := treePts_le_G Y hY (N + 1) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  unfold G at h
  have : N * (4 * Nat.clog 2 N + 1) ≤ 4 * N * (Nat.clog 2 N + 1) := by ring_nf; omega
  omega

end DetANN.HPIM.TP

open DetANN DetANN.HPIM in
theorem solution {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (hY : Function.Injective Y) :
    treePts Y (N + 1) Finset.univ ≤ 4 * N * (Nat.clog 2 N + 1) :=
  DetANN.HPIM.TP.tree_points' Y hY
