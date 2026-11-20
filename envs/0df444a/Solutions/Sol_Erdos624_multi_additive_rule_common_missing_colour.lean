-- Prove2me | solution 1 for Erdos624.multi_additive_rule_common_missing_colour
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:25:01.930483+00:00
-- url     : https://prove2.me/submissions/addb3a6a-e4b0-4180-bed2-6a2a161e9e2b

import Mathlib
open Finset Function

namespace E624R20A
open Finset Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {k : ℕ}

/-- Standard bilinear form on $(\mathbb F_2)^k$. -/
def dot (f v : Fin k → ZMod 2) : ZMod 2 := ∑ i : Fin k, f i * v i

def scale (c : ZMod 2) (v : Fin k → ZMod 2) : Fin k → ZMod 2 := fun i => c * v i

lemma dot_add (f v w : Fin k → ZMod 2) : dot f (v + w) = dot f v + dot f w := by
  simp [dot, mul_add, sum_add_distrib]

lemma dot_zero_right (f : Fin k → ZMod 2) : dot f 0 = 0 := by
  simp [dot]

lemma scale_zero (v : Fin k → ZMod 2) : scale 0 v = 0 := by
  funext i; simp [scale]

lemma scale_one (v : Fin k → ZMod 2) : scale 1 v = v := by
  funext i; simp [scale]

lemma dot_scale (f : Fin k → ZMod 2) (c : ZMod 2) (v : Fin k → ZMod 2) :
    dot f (scale c v) = c * dot f v := by
  simp [dot, scale, mul_assoc, mul_left_comm, mul_comm, mul_sum]

lemma dot_add_left (f g v : Fin k → ZMod 2) :
    dot (f + g) v = dot f v + dot g v := by
  simp [dot, add_mul, sum_add_distrib]

lemma dot_scale_left (c : ZMod 2) (f v : Fin k → ZMod 2) :
    dot (scale c f) v = c * dot f v := by
  simp [dot, scale, mul_assoc, mul_left_comm, mul_comm, mul_sum]

lemma dot_sum {α : Type*} [DecidableEq α]
    (f : Fin k → ZMod 2) (A : Finset α) (g : α → (Fin k → ZMod 2)) :
    dot f (∑ x ∈ A, g x) = ∑ x ∈ A, dot f (g x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [dot]
  | insert x A hx ih =>
    rw [sum_insert hx, sum_insert hx, dot_add, ih]

lemma card_V : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

lemma card_univ_V : #(univ : Finset (Fin k → ZMod 2)) = 2 ^ k := by
  simp [card_univ, card_V]

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  fin_cases a
  · rfl
  · decide

lemma eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have : a + b + b = b := by rw [h, zero_add]
  simpa [add_assoc, add_self_zmod2] using this

lemma add_left_cancel_zmod2 (a b : Fin k → ZMod 2) : a + b + a = b := by
  funext i
  have : a i + b i + a i = b i := by
    rw [add_assoc, add_left_comm, add_self_zmod2, add_zero]
  simpa [Pi.add_apply] using this

lemma addLeftEmbedding_add_cancel (a b : Fin k → ZMod 2) :
    addLeftEmbedding a (b + a) = b := by
  rw [addLeftEmbedding_apply]
  funext i
  have : a i + (b i + a i) = b i := by
    rw [add_left_comm, add_self_zmod2, add_zero]
  simpa [Pi.add_apply] using this

lemma exists_coord_one {u : Fin k → ZMod 2} (hu : u ≠ 0) :
    ∃ i : Fin k, u i = 1 := by
  by_contra hnone
  apply hu
  funext i
  have hne1 : u i ≠ 1 := fun h => hnone ⟨i, h⟩
  exact (zmod2_eq_zero_or_one (u i)).resolve_right hne1

lemma exists_dot_one {u : Fin k → ZMod 2} (hu : u ≠ 0) :
    ∃ f : Fin k → ZMod 2, dot f u = 1 := by
  obtain ⟨i0, hi0⟩ := exists_coord_one hu
  refine ⟨fun i => if i = i0 then 1 else 0, ?_⟩
  have huniv : (univ : Finset (Fin k)) = insert i0 (univ.erase i0) :=
    (insert_erase (mem_univ i0)).symm
  rw [dot, huniv, sum_insert (notMem_erase i0 univ)]
  simp [hi0, notMem_erase]

lemma dot_all_zero {u : Fin k → ZMod 2} (h : ∀ f, dot f u = 0) : u = 0 := by
  by_contra hu
  obtain ⟨f, hf⟩ := exists_dot_one hu
  exact zero_ne_one ((h f).symm.trans hf)

lemma card_dot_fiber {u : Fin k → ZMod 2} (hu : u ≠ 0) (b : ZMod 2) :
    #((univ : Finset (Fin k → ZMod 2)).filter (fun f => dot f u = b)) =
      2 ^ (k - 1) := by
  obtain ⟨f1, hf1⟩ := exists_dot_one hu
  let F : ZMod 2 → Finset (Fin k → ZMod 2) :=
    fun c => univ.filter (fun f => dot f u = c)
  have hunion : F 0 ∪ F 1 = univ := by
    ext f
    simp [F, mem_union, mem_filter]
    exact zmod2_eq_zero_or_one (dot f u)
  have hdis : Disjoint (F 0) (F 1) := by
    refine disjoint_left.2 fun f hf0 hf1 => ?_
    exact zero_ne_one (((mem_filter.1 hf0).2).symm.trans (mem_filter.1 hf1).2)
  have hswap : (F 0).map (addLeftEmbedding f1) = F 1 := by
    ext f
    constructor
    · intro hf
      rcases mem_map.1 hf with ⟨g, hg, rfl⟩
      have hg0 := (mem_filter.1 hg).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [addLeftEmbedding_apply, dot_add_left, hf1, hg0, add_zero]
    · intro hf
      have hfu := (mem_filter.1 hf).2
      refine mem_map.2 ⟨f + f1, ?_, addLeftEmbedding_add_cancel f1 f⟩
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [dot_add_left, hfu, hf1, add_self_zmod2]
  have hcard01 : #(F 0) = #(F 1) := by
    rw [← card_map (addLeftEmbedding f1), hswap]
  have hsum : #(F 0) + #(F 1) = 2 ^ k := by
    rw [← card_union_of_disjoint hdis, hunion, card_univ_V]
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h)
    apply hu
    subst k
    funext i
    exact i.elim0
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ (k - 1 + 1) := by rw [hks]
      _ = 2 ^ (k - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (k - 1) := mul_comm _ _
  have hF0 : #(F 0) = 2 ^ (k - 1) := by omega
  have hFb : #(F b) = 2 ^ (k - 1) := by
    rcases zmod2_eq_zero_or_one b with hb | hb
    · rw [hb, hF0]
    · rw [hb, ← hcard01, hF0]
  simpa [F] using hFb

lemma forms_multiple {u w : Fin k → ZMod 2}
    (h : ∀ f, dot f u = 0 → dot f w = 0) :
    w = 0 ∨ w = u := by
  by_cases hu : u = 0
  · left
    apply dot_all_zero
    intro f
    exact h f (by simp [hu, dot_zero_right])
  · obtain ⟨f1, hf1⟩ := exists_dot_one hu
    have hrep : ∀ f, dot f w = dot f u * dot f1 w := by
      intro f
      let g : Fin k → ZMod 2 := f + scale (dot f u) f1
      have hgu : dot g u = 0 := by
        simp only [g, dot_add_left, dot_scale_left, hf1, mul_one, add_self_zmod2]
      have : dot f w + dot f u * dot f1 w = 0 := by
        have hg := h g hgu
        simp only [g, dot_add_left, dot_scale_left] at hg
        exact hg
      exact eq_of_add_eq_zero this
    have hw' : w + scale (dot f1 w) u = 0 := by
      apply dot_all_zero
      intro f
      rw [dot_add, dot_scale, hrep f, mul_comm (dot f1 w)]
      exact add_self_zmod2 _
    have hw : w = scale (dot f1 w) u := by
      funext i
      have hzi := congrFun hw' i
      have hzi' : w i + scale (dot f1 w) u i = 0 := by
        simpa [Pi.add_apply] using hzi
      exact eq_of_add_eq_zero hzi'
    rcases zmod2_eq_zero_or_one (dot f1 w) with hd | hd
    · left
      rw [hw, hd, scale_zero]
    · right
      rw [hw, hd, scale_one]

lemma exists_ker_dot_one {u w : Fin k → ZMod 2}
    (hu : u ≠ 0) (hw0 : w ≠ 0) (hwu : w ≠ u) :
    ∃ f, dot f u = 0 ∧ dot f w = 1 := by
  by_contra hnone
  have : ∀ f, dot f u = 0 → dot f w = 0 := by
    intro f hu0
    have : dot f w ≠ 1 := fun h1 => hnone ⟨f, hu0, h1⟩
    exact (zmod2_eq_zero_or_one (dot f w)).resolve_right this
  rcases forms_multiple this with h | h
  · exact hw0 h
  · exact hwu h

def keepSet (u w : Fin k → ZMod 2) : Finset (Fin k → ZMod 2) :=
  univ.filter (fun f => dot f u = 1 ∧ dot f w = 0)

lemma card_keep_ne {u w : Fin k → ZMod 2}
    (hu : u ≠ 0) (hwu : w ≠ u) (hk : 2 ≤ k) :
    2 ^ (k - 2) ≤ #(keepSet u w) := by
  by_cases hw0 : w = 0
  · subst w
    have hEq : keepSet u 0 =
        (univ : Finset (Fin k → ZMod 2)).filter (fun f => dot f u = 1) := by
      ext f; simp [keepSet, dot_zero_right]
    rw [hEq, card_dot_fiber hu 1]
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, pow_succ]
    exact Nat.le_mul_of_pos_right (2 ^ (k - 2)) (by decide : (0 : ℕ) < 2)
  · obtain ⟨f0, hf0u, hf0w⟩ := exists_ker_dot_one hu hw0 hwu
    let K0 := keepSet u w
    let K1 : Finset (Fin k → ZMod 2) :=
      univ.filter (fun f => dot f u = 1 ∧ dot f w = 1)
    have hswap : K0.map (addLeftEmbedding f0) = K1 := by
      ext f
      constructor
      · intro hf
        rcases mem_map.1 hf with ⟨g, hg, rfl⟩
        have hg' := mem_filter.1 hg
        refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
        · rw [addLeftEmbedding_apply, dot_add_left, hf0u, hg'.2.1, zero_add]
        · rw [addLeftEmbedding_apply, dot_add_left, hf0w, hg'.2.2, add_zero]
      · intro hf
        have hf' := mem_filter.1 hf
        refine mem_map.2 ⟨f + f0, ?_, addLeftEmbedding_add_cancel f0 f⟩
        refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
        · rw [dot_add_left, hf'.2.1, hf0u, add_zero]
        · rw [dot_add_left, hf'.2.2, hf0w, add_self_zmod2]
    have hcard : #K0 = #K1 := by
      rw [← card_map (addLeftEmbedding f0), hswap]
    have hunion : K0 ∪ K1 =
        (univ : Finset (Fin k → ZMod 2)).filter (fun f => dot f u = 1) := by
      ext f
      constructor
      · intro hf
        rcases mem_union.1 hf with h | h
        · exact mem_filter.2 ⟨mem_univ f, (mem_filter.1 h).2.1⟩
        · exact mem_filter.2 ⟨mem_univ f, (mem_filter.1 h).2.1⟩
      · intro hf
        have hu1 : dot f u = 1 := (mem_filter.1 hf).2
        rcases zmod2_eq_zero_or_one (dot f w) with hw | hw
        · exact mem_union.2 (Or.inl (mem_filter.2 ⟨mem_univ f, hu1, hw⟩))
        · exact mem_union.2 (Or.inr (mem_filter.2 ⟨mem_univ f, hu1, hw⟩))
    have hdis : Disjoint K0 K1 := by
      refine disjoint_left.2 fun f hf0 hf1 => ?_
      exact zero_ne_one
        (((mem_filter.1 hf0).2.2).symm.trans (mem_filter.1 hf1).2.2)
    have hsum : #K0 + #K1 = 2 ^ (k - 1) := by
      rw [← card_union_of_disjoint hdis, hunion, card_dot_fiber hu 1]
    have hpow : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      have : k - 1 = (k - 2) + 1 := by omega
      rw [this, pow_succ, mul_comm]
    have : #K0 = 2 ^ (k - 2) := by omega
    exact le_of_eq this.symm

lemma exists_ge_avg {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → ℕ) :
    ∃ a ∈ S, ∑ x ∈ S, f x ≤ f a * #S := by
  by_contra hnone
  have hall : ∀ a ∈ S, f a * #S + 1 ≤ ∑ x ∈ S, f x := by
    intro a ha
    have : ¬ ∑ x ∈ S, f x ≤ f a * #S := fun h => hnone ⟨a, ha, h⟩
    omega
  have : (∑ a ∈ S, f a) * #S + #S ≤ (∑ a ∈ S, f a) * #S := by
    have hL : ∑ a ∈ S, (f a * #S + 1) = (∑ a ∈ S, f a) * #S + #S := by
      rw [sum_add_distrib, ← sum_mul]
      have h1 : ∑ _a ∈ S, (1 : ℕ) = #S * 1 := sum_const_nat (fun _ _ => rfl)
      rw [h1, mul_one]
    have hR : ∑ a ∈ S, (∑ x ∈ S, f x) = (∑ x ∈ S, f x) * #S := by
      rw [sum_const_nat (fun _ _ => rfl), mul_comm]
    have hle := sum_le_sum (fun a ha => hall a ha)
    rwa [hL, hR] at hle
  have hpos : 0 < #S := card_pos.mpr hS
  omega

lemma exists_le_avg {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → ℕ) :
    ∃ a ∈ S, f a * #S ≤ ∑ x ∈ S, f x := by
  by_contra hnone
  have hall : ∀ a ∈ S, ∑ x ∈ S, f x + 1 ≤ f a * #S := by
    intro a ha
    have : ¬ f a * #S ≤ ∑ x ∈ S, f x := fun h => hnone ⟨a, ha, h⟩
    omega
  have : (∑ a ∈ S, f a) * #S + #S ≤ (∑ a ∈ S, f a) * #S := by
    have hL : ∑ a ∈ S, (∑ x ∈ S, f x + 1) = (∑ x ∈ S, f x) * #S + #S := by
      rw [sum_add_distrib]
      have hs : ∑ _a ∈ S, (∑ x ∈ S, f x) = #S * ∑ x ∈ S, f x :=
        sum_const_nat (fun _ _ => rfl)
      have h1 : ∑ _a ∈ S, (1 : ℕ) = #S * 1 := sum_const_nat (fun _ _ => rfl)
      rw [hs, h1, mul_one, mul_comm (∑ x ∈ S, f x)]
    have hR : ∑ a ∈ S, (f a * #S) = (∑ a ∈ S, f a) * #S := (sum_mul _ _ _).symm
    have hle := sum_le_sum (fun a ha => hall a ha)
    rwa [hL, hR] at hle
  have hpos : 0 < #S := card_pos.mpr hS
  omega

lemma two_t_bound {t N M b : ℕ}
    (ht : 2 * t < N) (hM : N - t ≤ M) (hb : b * M ≤ N * t) :
    b ≤ 2 * t := by
  by_contra hlt
  have hb1 : 2 * t + 1 ≤ b := by omega
  have htN : t < N := by omega
  have hpos : 0 < N - t := Nat.sub_pos_of_lt htN
  have hle : (2 * t + 1) * (N - t) ≤ N * t := by
    have : (2 * t + 1) * (N - t) ≤ (2 * t + 1) * M :=
      Nat.mul_le_mul_left _ hM
    have : (2 * t + 1) * M ≤ b * M := Nat.mul_le_mul_right _ hb1
    omega
  have hge : N * t + N ≤ (2 * t + 1) * (N - t) := by
    -- (2t+1)(N-t) = (2t+1)N - (2t+1)t and this is ≥ Nt + N
    have hdist : (2 * t + 1) * (N - t) = (2 * t + 1) * N - (2 * t + 1) * t :=
      Nat.mul_sub_left_distrib _ _ _
    have hle' : (2 * t + 1) * t ≤ (2 * t + 1) * N :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt htN)
    -- (2t+1)N - (2t+1)t ≥ Nt + N  iff  (2t+1)N ≥ Nt + N + (2t+1)t
    -- iff  2t N + N ≥ N t + N + 2t^2 + t  iff  t N ≥ 2t^2 + t  iff  N ≥ 2t + 1
    have hNt : 2 * t + 1 ≤ N := Nat.succ_le_of_lt ht
    have : (2 * t + 1) * N ≥ N * t + N + (2 * t + 1) * t := by
      --  (2t+1)N = 2t N + N
      --  right = Nt + N + 2t^2 + t
      --  2t N + N - Nt - N = t N ≥ 2t^2 + t = t(2t+1)
      --  since N ≥ 2t+1
      nlinarith
    omega
  omega

lemma sum_card_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (p : α → β → Prop) [DecidableRel p] :
    ∑ a ∈ S, #(T.filter (fun b => p a b)) = ∑ b ∈ T, #(S.filter (fun a => p a b)) := by
  classical
  have hS : ∀ a ∈ S, #(T.filter (fun b => p a b)) =
      ∑ b ∈ T, if p a b then 1 else 0 := by
    intro a ha
    rw [← sum_filter (p := fun b => p a b), card_eq_sum_ones]
  have hT : ∀ b ∈ T, #(S.filter (fun a => p a b)) =
      ∑ a ∈ S, if p a b then 1 else 0 := by
    intro b hb
    rw [← sum_filter (p := fun a => p a b), card_eq_sum_ones]
  calc
    ∑ a ∈ S, #(T.filter (fun b => p a b))
        = ∑ a ∈ S, ∑ b ∈ T, if p a b then 1 else 0 := sum_congr rfl hS
    _ = ∑ b ∈ T, ∑ a ∈ S, if p a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ T, #(S.filter (fun a => p a b)) :=
      sum_congr rfl (fun b hb => (hT b hb).symm)

/-- A colouring assembled from fewer than $n/2$ additive $\mathbb F_2^k$-rules
(arbitrary weights and colour relabellings, with an unrestricted choice of rule
on each subset) always misses some colour on all subsets of a set of size at
least $(n-2t)/2^t$. This does not address unrestricted colourings, and in
particular it does not prove $H(2^k)>k+1$. -/
theorem multi_additive_rule_common_missing_colour
    (k t : ℕ) (ht : 2 * t < 2 ^ k)
    (w : Fin t → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (π : Fin t → ((Fin k → ZMod 2) ≃ (Fin k → ZMod 2))) :
    ∃ (c : Fin k → ZMod 2) (Y : Finset (Fin k → ZMod 2)),
      2 ^ t * #Y + 2 * t ≥ 2 ^ k ∧
        ∀ A ⊆ Y, ∀ j : Fin t, π j (∑ x ∈ A, w j x) ≠ c := by
  classical
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst t
    refine ⟨0, univ, ?_, ?_⟩
    · simp [card_univ_V]
    · intro A hA j
      exact j.elim0
  have hk : 2 ≤ k := by
    cases k with
    | zero =>
      have : 2 * t < 1 := by simpa using ht
      omega
    | succ k' =>
      cases k' with
      | zero =>
        have : 2 * t < 2 := by simpa using ht
        omega
      | succ _ => omega
  -- remaining colours, after excluding π_j(0)
  let excl : Finset (Fin k → ZMod 2) :=
    (univ : Finset (Fin t)).image (fun j => π j 0)
  have hexcl : #excl ≤ t :=
    (card_image_le).trans (by simp [card_univ, Fintype.card_fin])
  let rem : Finset (Fin k → ZMod 2) := univ \ excl
  have hrem : 2 ^ k - t ≤ #rem := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ_V]
    omega
  have hrem_pos : rem.Nonempty := by
    have : t < 2 ^ k := by omega
    have : 0 < 2 ^ k - t := Nat.sub_pos_of_lt this
    exact card_pos.mp (by omega)
  let bad : (Fin k → ZMod 2) → Finset (Fin k → ZMod 2) :=
    fun c => univ.filter (fun x => ∃ j : Fin t, π j (w j x) = c)
  have hsum_bad : ∑ c ∈ rem, #(bad c) ≤ 2 ^ k * t := by
    have hswap :
        ∑ c ∈ rem, #(bad c) =
          ∑ x ∈ (univ : Finset (Fin k → ZMod 2)),
            #{c ∈ rem | ∃ j : Fin t, π j (w j x) = c} := by
      simpa [bad] using
        (sum_card_filter_comm rem
          (univ : Finset (Fin k → ZMod 2))
          (fun c x => ∃ j : Fin t, π j (w j x) = c))
    have hpt : ∀ x, #{c ∈ rem | ∃ j : Fin t, π j (w j x) = c} ≤ t := by
      intro x
      have hsub :
          (rem.filter (fun c => ∃ j : Fin t, π j (w j x) = c)) ⊆
            (univ : Finset (Fin t)).image (fun j => π j (w j x)) := by
        intro c hc
        obtain ⟨j, hj⟩ := (mem_filter.1 hc).2
        exact mem_image.2 ⟨j, mem_univ j, hj⟩
      exact (card_le_card hsub).trans
        ((card_image_le).trans (by simp [card_univ, Fintype.card_fin]))
    rw [hswap]
    have : ∑ x ∈ (univ : Finset (Fin k → ZMod 2)),
        #{c ∈ rem | ∃ j : Fin t, π j (w j x) = c} ≤
          ∑ _x ∈ (univ : Finset (Fin k → ZMod 2)), t :=
      sum_le_sum fun x _ => hpt x
    simpa [sum_const, smul_eq_mul, card_univ_V, mul_comm] using this
  obtain ⟨c, hc_rem, hcbound⟩ := exists_le_avg rem hrem_pos (fun c => #(bad c))
  have hbad : #(bad c) ≤ 2 * t :=
    two_t_bound (N := 2 ^ k) (M := #rem) (b := #(bad c)) ht hrem
      (by
        have : #(bad c) * #rem ≤ ∑ x ∈ rem, #(bad x) := hcbound
        exact this.trans hsum_bad)
  let Good : Finset (Fin k → ZMod 2) := univ \ bad c
  have hGood : 2 ^ k - 2 * t ≤ #Good := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ_V]
    have : #(bad c) ≤ 2 * t := hbad
    have : #(bad c) ≤ 2 ^ k := by
      have : #(bad c) ≤ #(univ : Finset (Fin k → ZMod 2)) := card_filter_le _ _
      simpa [card_univ_V] using this
    omega
  let u : Fin t → (Fin k → ZMod 2) := fun j => (π j).symm c
  have hu : ∀ j, u j ≠ 0 := by
    intro j hj
    have : c = π j 0 := by
      have : π j (u j) = c := Equiv.apply_symm_apply (π j) c
      simpa [u, hj] using this.symm
    have : c ∈ excl := mem_image.2 ⟨j, mem_univ j, this.symm⟩
    exact (mem_sdiff.1 hc_rem).2 this
  have hwu : ∀ x ∈ Good, ∀ j, w j x ≠ u j := by
    intro x hx j hwu
    have : x ∈ bad c := by
      refine mem_filter.2 ⟨mem_univ x, ⟨j, ?_⟩⟩
      have : π j (u j) = c := Equiv.apply_symm_apply (π j) c
      simpa [hwu] using this
    exact (mem_sdiff.1 hx).2 this
  -- linear functionals
  let Phi : Finset (Fin t → (Fin k → ZMod 2)) :=
    Fintype.piFinset (fun j => univ.filter (fun f => dot f (u j) = 1))
  have hPhi_card : #Phi = 2 ^ ((k - 1) * t) := by
    simp only [Phi]
    rw [Fintype.card_piFinset]
    have hs : ∀ j, #((univ : Finset (Fin k → ZMod 2)).filter
        (fun f => dot f (u j) = 1)) = 2 ^ (k - 1) :=
      fun j => card_dot_fiber (hu j) 1
    have : ∏ j : Fin t, #((univ : Finset (Fin k → ZMod 2)).filter
        (fun f => dot f (u j) = 1)) = ∏ _j : Fin t, 2 ^ (k - 1) :=
      prod_congr rfl (fun j _ => hs j)
    rw [this, prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  have hPhi_pos : Phi.Nonempty := by
    have : 0 < 2 ^ ((k - 1) * t) := Nat.pow_pos (by decide : (0 : ℕ) < 2)
    exact card_pos.mp (by simpa [hPhi_card] using this)
  let YF : (Fin t → (Fin k → ZMod 2)) → Finset (Fin k → ZMod 2) :=
    fun F => Good.filter (fun x => ∀ j : Fin t, dot (F j) (w j x) = 0)
  have hkeep_card : ∀ x ∈ Good,
      2 ^ ((k - 2) * t) ≤
        #(Fintype.piFinset (fun j => keepSet (u j) (w j x))) := by
    intro x hx
    rw [Fintype.card_piFinset]
    have hj : ∀ j, 2 ^ (k - 2) ≤ #(keepSet (u j) (w j x)) :=
      fun j => card_keep_ne (hu j) (hwu x hx j) hk
    have : ∏ _j : Fin t, 2 ^ (k - 2) ≤ ∏ j, #(keepSet (u j) (w j x)) :=
      prod_le_prod' (fun j _ => hj j)
    simpa [prod_const, card_univ, Fintype.card_fin, pow_mul] using this
  have hfiber : ∀ x ∈ Good,
      #{F ∈ Phi | ∀ j : Fin t, dot (F j) (w j x) = 0} =
        #(Fintype.piFinset (fun j => keepSet (u j) (w j x))) := by
    intro x hx
    have hEq :
        Phi.filter (fun F => ∀ j : Fin t, dot (F j) (w j x) = 0) =
          Fintype.piFinset (fun j => keepSet (u j) (w j x)) := by
      ext F
      constructor
      · intro hF
        have hf := mem_filter.1 hF
        refine Fintype.mem_piFinset.2 fun j => ?_
        have hmem := Fintype.mem_piFinset.1 hf.1 j
        exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hmem).2, hf.2 j⟩
      · intro hF
        refine mem_filter.2 ⟨?_, ?_⟩
        · refine Fintype.mem_piFinset.2 fun j => ?_
          have hj := Fintype.mem_piFinset.1 hF j
          exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hj).2.1⟩
        · intro j
          exact (mem_filter.1 (Fintype.mem_piFinset.1 hF j)).2.2
    rw [hEq]
  have hsumY : #Good * 2 ^ ((k - 2) * t) ≤ ∑ F ∈ Phi, #(YF F) := by
    have hsw :
        ∑ F ∈ Phi, #(YF F) =
          ∑ x ∈ Good, #{F ∈ Phi | ∀ j : Fin t, dot (F j) (w j x) = 0} := by
      simpa [YF] using
        (sum_card_filter_comm Phi Good
          (fun F x => ∀ j : Fin t, dot (F j) (w j x) = 0))
    have hconst : ∑ _x ∈ Good, 2 ^ ((k - 2) * t) = #Good * 2 ^ ((k - 2) * t) :=
      sum_const_nat (fun _ _ => rfl)
    have hle : ∑ _x ∈ Good, 2 ^ ((k - 2) * t) ≤
        ∑ x ∈ Good, #{F ∈ Phi | ∀ j : Fin t, dot (F j) (w j x) = 0} :=
      sum_le_sum fun x hx => by
        rw [hfiber x hx]
        exact hkeep_card x hx
    rw [← hconst, hsw]
    exact hle
  obtain ⟨F, hF, hFge⟩ := exists_ge_avg Phi hPhi_pos (fun F => #(YF F))
  have hYsize : 2 ^ t * #(YF F) ≥ #Good := by
    have h1 : #Good * 2 ^ ((k - 2) * t) ≤ #(YF F) * 2 ^ ((k - 1) * t) := by
      have : ∑ G ∈ Phi, #(YF G) ≤ #(YF F) * #Phi := hFge
      have := hsumY.trans this
      simpa [hPhi_card] using this
    have hpow : (k - 1) * t = (k - 2) * t + t := by
      have : k - 1 = (k - 2) + 1 := by omega
      rw [this, add_mul, one_mul]
    have h2 : #Good * 2 ^ ((k - 2) * t) ≤
        #(YF F) * (2 ^ ((k - 2) * t) * 2 ^ t) := by
      rwa [hpow, pow_add] at h1
    have h3 : #Good * 2 ^ ((k - 2) * t) ≤
        (#(YF F) * 2 ^ t) * 2 ^ ((k - 2) * t) := by
      convert h2 using 1
      ac_rfl
    have hpos : 0 < 2 ^ ((k - 2) * t) := Nat.pow_pos (by decide : (0 : ℕ) < 2)
    have := Nat.le_of_mul_le_mul_right h3 hpos
    simpa [mul_comm] using this
  refine ⟨c, YF F, ?_, ?_⟩
  · have h1 : 2 ^ k - 2 * t ≤ 2 ^ t * #(YF F) := le_trans hGood hYsize
    have h2 : 2 ^ k - 2 * t + 2 * t = 2 ^ k :=
      Nat.sub_add_cancel (Nat.le_of_lt ht)
    omega
  · intro A hA j
    have hlin : dot (F j) (∑ x ∈ A, w j x) = ∑ x ∈ A, dot (F j) (w j x) :=
      dot_sum (F j) A (w j)
    have hzero : ∑ x ∈ A, dot (F j) (w j x) = 0 := by
      have : ∀ x ∈ A, dot (F j) (w j x) = 0 := by
        intro x hx
        have hxY : x ∈ YF F := hA hx
        exact (mem_filter.1 hxY).2 j
      exact sum_eq_zero this
    have hF1 : dot (F j) (u j) = 1 := by
      have hmem := Fintype.mem_piFinset.1 hF j
      exact (mem_filter.1 hmem).2
    intro hEq
    have hsumu : ∑ x ∈ A, w j x = u j := by
      have : (π j).symm (π j (∑ x ∈ A, w j x)) = (π j).symm c := by
        rw [hEq]
      simpa [Equiv.symm_apply_apply] using this
    have : (1 : ZMod 2) = 0 := by
      calc
        1 = dot (F j) (u j) := hF1.symm
        _ = dot (F j) (∑ x ∈ A, w j x) := by rw [hsumu]
        _ = 0 := by rw [hlin, hzero]
    exact zero_ne_one this.symm

end E624R20A

namespace Erdos624

theorem multi_additive_rule_common_missing_colour
    (k t : ℕ) (ht : 2 * t < 2 ^ k)
    (w : Fin t → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (π : Fin t → ((Fin k → ZMod 2) ≃ (Fin k → ZMod 2))) :
    ∃ (c : Fin k → ZMod 2) (Y : Finset (Fin k → ZMod 2)),
      2 ^ t * #Y + 2 * t ≥ 2 ^ k ∧
        ∀ A ⊆ Y, ∀ j : Fin t, π j (∑ x ∈ A, w j x) ≠ c :=
  E624R20A.multi_additive_rule_common_missing_colour k t ht w π

end Erdos624

open Finset

theorem solution
    (k t : ℕ) (ht : 2 * t < 2 ^ k)
    (w : Fin t → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (π : Fin t → ((Fin k → ZMod 2) ≃ (Fin k → ZMod 2))) :
    ∃ (c : Fin k → ZMod 2) (Y : Finset (Fin k → ZMod 2)),
      2 ^ t * #Y + 2 * t ≥ 2 ^ k ∧
        ∀ A ⊆ Y, ∀ j : Fin t, π j (∑ x ∈ A, w j x) ≠ c :=
  Erdos624.multi_additive_rule_common_missing_colour k t ht w π
