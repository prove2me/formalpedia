-- Prove2me | solution 1 for BartlettNN.FatNet.lemma20_l2_covering_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:09:05.622161+00:00
-- url     : https://prove2.me/submissions/3be58fbe-2cb2-4af6-96b9-b0ecc27e9f04

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_coverNum

set_option autoImplicit false

namespace L20dd4c

open Classical

noncomputable def Sh (B : ℕ) {m : ℕ} (S : Finset (Fin m → ℕ)) :
    Finset (Finset (Fin m) × (Fin m → ℕ)) :=
  ((Finset.univ : Finset (Finset (Fin m))) ×ˢ
      Fintype.piFinset (fun _ : Fin m => Finset.range (B+1))).filter
   (fun p => (∀ i, i ∉ p.1 → p.2 i = 0) ∧ (∀ i ∈ p.1, p.2 i + 2 ≤ B) ∧
     ∀ c : Fin m → Bool, ∃ h ∈ S, ∀ i ∈ p.1,
       (c i = true → p.2 i + 2 ≤ h i) ∧ (c i = false → h i ≤ p.2 i))

lemma mem_Sh {B m : ℕ} {S : Finset (Fin m → ℕ)} {p : Finset (Fin m) × (Fin m → ℕ)} :
    p ∈ Sh B S ↔ (∀ i, i ∉ p.1 → p.2 i = 0) ∧ (∀ i ∈ p.1, p.2 i + 2 ≤ B) ∧
     ∀ c : Fin m → Bool, ∃ h ∈ S, ∀ i ∈ p.1,
       (c i = true → p.2 i + 2 ≤ h i) ∧ (c i = false → h i ≤ p.2 i) := by
  unfold Sh
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, h1, h2, h3⟩
    by_cases hi : i ∈ p.1
    · have := h2 i hi; omega
    · rw [h1 i hi]; omega

lemma Sh_mono {B m : ℕ} {S S' : Finset (Fin m → ℕ)} (h : S ⊆ S') : Sh B S ⊆ Sh B S' := by
  intro p hp
  rw [mem_Sh] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨h1, h2, fun c => ?_⟩
  obtain ⟨g, hg, hg'⟩ := h3 c
  exact ⟨g, h hg, hg'⟩

lemma not_mem_of_const {B m : ℕ} {S : Finset (Fin m → ℕ)} {i : Fin m} {j : ℕ}
    (hS : ∀ h ∈ S, h i = j) {p : Finset (Fin m) × (Fin m → ℕ)} (hp : p ∈ Sh B S) :
    i ∉ p.1 := by
  intro hi
  rw [mem_Sh] at hp
  obtain ⟨_, _, h3⟩ := hp
  obtain ⟨g1, hg1, hg1'⟩ := h3 (fun _ => true)
  obtain ⟨g2, hg2, hg2'⟩ := h3 (fun _ => false)
  have a := (hg1' i hi).1 rfl
  have b := (hg2' i hi).2 rfl
  rw [hS g1 hg1] at a
  rw [hS g2 hg2] at b
  omega

def extP {m : ℕ} (i : Fin m) (j : ℕ) (p : Finset (Fin m) × (Fin m → ℕ)) :
    Finset (Fin m) × (Fin m → ℕ) :=
  (insert i p.1, Function.update p.2 i j)

lemma ext_mem {B m : ℕ} {F1 F2 : Finset (Fin m → ℕ)} {i : Fin m} {j1 j2 : ℕ}
    (h1 : ∀ h ∈ F1, h i = j1) (h2 : ∀ h ∈ F2, h i = j2) (hj : j1 + 2 ≤ j2) (hjB : j2 ≤ B)
    {p : Finset (Fin m) × (Fin m → ℕ)} (hp1 : p ∈ Sh B F1) (hp2 : p ∈ Sh B F2) :
    extP i j1 p ∈ Sh B (F1 ∪ F2) := by
  have hi : i ∉ p.1 := not_mem_of_const h1 hp1
  rw [mem_Sh] at hp1 hp2 ⊢
  obtain ⟨a1, a2, a3⟩ := hp1
  obtain ⟨_, _, b3⟩ := hp2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [extP, Finset.mem_insert, not_or] at hx
    simp only [extP, Function.update_apply, if_neg hx.1]
    exact a1 x hx.2
  · intro x hx
    simp only [extP, Finset.mem_insert] at hx
    simp only [extP, Function.update_apply]
    by_cases hxi : x = i
    · rw [if_pos hxi]; omega
    · rw [if_neg hxi]
      exact a2 x (hx.resolve_left hxi)
  · intro c
    cases hc : c i
    · obtain ⟨g, hg, hg'⟩ := a3 c
      refine ⟨g, Finset.mem_union_left _ hg, ?_⟩
      intro x hx
      simp only [extP, Finset.mem_insert] at hx
      simp only [extP, Function.update_apply]
      by_cases hxi : x = i
      · rw [if_pos hxi, hxi, hc, h1 g hg]
        exact ⟨fun h => by simp at h, fun _ => le_rfl⟩
      · rw [if_neg hxi]
        exact hg' x (hx.resolve_left hxi)
    · obtain ⟨g, hg, hg'⟩ := b3 c
      refine ⟨g, Finset.mem_union_right _ hg, ?_⟩
      intro x hx
      simp only [extP, Finset.mem_insert] at hx
      simp only [extP, Function.update_apply]
      by_cases hxi : x = i
      · rw [if_pos hxi, hxi, hc, h2 g hg]
        exact ⟨fun _ => hj, fun h => by simp at h⟩
      · rw [if_neg hxi]
        exact hg' x (hx.resolve_left hxi)

lemma step_card {B m : ℕ} {F1 F2 S : Finset (Fin m → ℕ)} {i : Fin m} {j1 j2 : ℕ}
    (h1 : ∀ h ∈ F1, h i = j1) (h2 : ∀ h ∈ F2, h i = j2) (hj : j1 + 2 ≤ j2) (hjB : j2 ≤ B)
    (hsub : F1 ∪ F2 ⊆ S) : (Sh B F1).card + (Sh B F2).card ≤ (Sh B S).card := by
  set I := Sh B F1 ∩ Sh B F2 with hI
  have hinj : Set.InjOn (extP i j1) (I : Set _) := by
    intro p hp q hq hpq
    simp only [hI, Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hp hq
    have hip := not_mem_of_const h1 hp.1
    have hiq := not_mem_of_const h1 hq.1
    have pz := (mem_Sh.1 hp.1).1 i hip
    have qz := (mem_Sh.1 hq.1).1 i hiq
    simp only [extP, Prod.mk.injEq] at hpq
    obtain ⟨e1, e2⟩ := hpq
    refine Prod.ext ?_ ?_
    · ext x
      by_cases hxi : x = i
      · rw [hxi]; simp [hip, hiq]
      · have := Finset.ext_iff.mp e1 x
        simpa [hxi] using this
    · funext x
      by_cases hxi : x = i
      · rw [hxi, pz, qz]
      · have := congrFun e2 x
        simpa [Function.update_apply, hxi] using this
  have hdisj : Disjoint (Sh B F1 ∪ Sh B F2) (I.image (extP i j1)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_image] at hp'
    obtain ⟨q, _, rfl⟩ := hp'
    have : i ∈ (extP i j1 q).1 := Finset.mem_insert_self _ _
    rcases Finset.mem_union.1 hp with hp | hp
    · exact not_mem_of_const h1 hp this
    · exact not_mem_of_const h2 hp this
  have hsub' : (Sh B F1 ∪ Sh B F2) ∪ I.image (extP i j1) ⊆ Sh B S := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact Sh_mono (Finset.subset_union_left.trans hsub) hp
      · exact Sh_mono (Finset.subset_union_right.trans hsub) hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      rw [hI, Finset.mem_inter] at hq
      exact Sh_mono hsub (ext_mem h1 h2 hj hjB hq.1 hq.2)
  calc (Sh B F1).card + (Sh B F2).card = (Sh B F1 ∪ Sh B F2).card + I.card :=
        (Finset.card_union_add_card_inter _ _).symm
    _ = (Sh B F1 ∪ Sh B F2).card + (I.image (extP i j1)).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ = ((Sh B F1 ∪ Sh B F2) ∪ I.image (extP i j1)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub'

lemma pigeon {B m K t : ℕ} (S : Finset (Fin m → ℕ)) (hB : ∀ h ∈ S, ∀ i, h i ≤ B)
    (hsep : ∀ f ∈ S, ∀ g ∈ S, f ≠ g → ∃ i, f i + 2 ≤ g i ∨ g i + 2 ≤ f i)
    (hK : m * (B+1)^2 ≤ K) (ht : K * (t - 1) < S.card - 1) :
    ∃ i j1 j2, j1 + 2 ≤ j2 ∧ t ≤ (S.filter (fun h => h i = j1)).card ∧
      t ≤ (S.filter (fun h => h i = j2)).card ∧ j2 ≤ B := by
  obtain ⟨f0, hf0, g0, hg0, hfg0⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  obtain ⟨i0, _⟩ := hsep f0 hf0 g0 hg0 hfg0
  obtain ⟨idx, hidx⟩ : ∃ idx : (Fin m → ℕ) × (Fin m → ℕ) → Fin m, ∀ f ∈ S, ∀ g ∈ S, f ≠ g →
      (f (idx (f, g)) + 2 ≤ g (idx (f, g)) ∨ g (idx (f, g)) + 2 ≤ f (idx (f, g))) := by
    refine ⟨fun pr => if h : ∃ i, pr.1 i + 2 ≤ pr.2 i ∨ pr.2 i + 2 ≤ pr.1 i then h.choose
      else i0, fun f hf g hg hfg => ?_⟩
    have h := hsep f hf g hg hfg
    dsimp only
    rw [dif_pos h]
    exact h.choose_spec
  set n := S.card with hn
  set w : (Fin m → ℕ) × (Fin m → ℕ) → Fin m × ℕ × ℕ :=
    fun pr => (idx pr, pr.1 (idx pr), pr.2 (idx pr)) with hw
  set tt : Finset (Fin m × ℕ × ℕ) :=
    (Finset.univ : Finset (Fin m)) ×ˢ (Finset.range (B+1) ×ˢ Finset.range (B+1)) with htt
  have hmaps : ∀ a ∈ S.offDiag, w a ∈ tt := by
    intro a ha
    rw [Finset.mem_offDiag] at ha
    simp only [hw, htt, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    exact ⟨Nat.lt_succ_of_le (hB _ ha.1 _), Nat.lt_succ_of_le (hB _ ha.2.1 _)⟩
  have httc : tt.card ≤ K := by
    simp only [htt, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range]
    calc m * ((B+1) * (B+1)) = m * (B+1)^2 := by ring
      _ ≤ K := hK
  have hlt : tt.card * (n * (t - 1)) < S.offDiag.card := by
    rw [Finset.offDiag_card, ← hn]
    obtain ⟨b, hb⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
    rw [hb] at ht ⊢
    have e : (b + 1) * (b + 1) - (b + 1) = (b + 1) * b := by
      rw [Nat.mul_succ]; omega
    rw [e]
    simp only [Nat.add_sub_cancel] at ht
    calc tt.card * ((b + 1) * (t - 1)) ≤ K * ((b + 1) * (t - 1)) := Nat.mul_le_mul_right _ httc
      _ = (b + 1) * (K * (t - 1)) := by ring
      _ < (b + 1) * b := by nlinarith
  obtain ⟨⟨i, j1, j2⟩, _, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  set fib := S.offDiag.filter (fun x => w x = (i, j1, j2)) with hfib
  have hmemfib : ∀ pr ∈ fib, pr.1 ∈ S ∧ pr.2 ∈ S ∧ pr.1 ≠ pr.2 ∧ idx pr = i ∧
      pr.1 i = j1 ∧ pr.2 i = j2 := by
    intro pr hpr
    rw [hfib, Finset.mem_filter, Finset.mem_offDiag] at hpr
    obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hpr
    simp only [hw, Prod.mk.injEq] at a4
    obtain ⟨b1, b2, b3⟩ := a4
    rw [b1] at b2 b3
    exact ⟨a1, a2, a3, b1, b2, b3⟩
  have hsub1 : fib ⊆ (S.filter (fun h => h i = j1)) ×ˢ S := by
    intro pr hpr
    obtain ⟨a1, a2, _, _, a5, _⟩ := hmemfib pr hpr
    rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨a1, a5⟩, a2⟩
  have hsub2 : fib ⊆ S ×ˢ (S.filter (fun h => h i = j2)) := by
    intro pr hpr
    obtain ⟨a1, a2, _, _, _, a6⟩ := hmemfib pr hpr
    rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨a1, ⟨a2, a6⟩⟩
  have c1 := Finset.card_le_card hsub1
  have c2 := Finset.card_le_card hsub2
  rw [Finset.card_product] at c1 c2
  have hn0 : 0 < n := by omega
  have k1 : t ≤ (S.filter (fun h => h i = j1)).card := by
    have : n * (t - 1) < (S.filter (fun h => h i = j1)).card * n := lt_of_lt_of_le hy c1
    have : (t - 1) < (S.filter (fun h => h i = j1)).card := by
      by_contra hc; rw [not_lt] at hc
      have := Nat.mul_le_mul_left n hc
      linarith [mul_comm n (S.filter (fun h => h i = j1)).card]
    omega
  have k2 : t ≤ (S.filter (fun h => h i = j2)).card := by
    have : n * (t - 1) < n * (S.filter (fun h => h i = j2)).card := lt_of_lt_of_le hy c2
    have : (t - 1) < (S.filter (fun h => h i = j2)).card := by
      by_contra hc; rw [not_lt] at hc
      have := Nat.mul_le_mul_left n hc
      linarith
    omega
  obtain ⟨pr, hpr⟩ : fib.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hmemfib pr hpr
  have hs := hidx pr.1 a1 pr.2 a2 a3
  rw [a4, a5, a6] at hs
  have hb1 : j1 ≤ B := a5 ▸ hB _ a1 i
  have hb2 : j2 ≤ B := a6 ▸ hB _ a2 i
  rcases hs with hs | hs
  · exact ⟨i, j1, j2, hs, k1, k2, hb2⟩
  · exact ⟨i, j2, j1, hs, k2, k1, hb1⟩

def T (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | r+1 => 2 * K^r

lemma core {B m K : ℕ} (hK : m * (B+1)^2 ≤ K) (hK2 : 2 ≤ K) : ∀ (r : ℕ) (S : Finset (Fin m → ℕ)),
    (∀ h ∈ S, ∀ i, h i ≤ B) → (∀ f ∈ S, ∀ g ∈ S, f ≠ g → ∃ i, f i + 2 ≤ g i ∨ g i + 2 ≤ f i) →
    T K r ≤ S.card → 2^r ≤ (Sh B S).card := by
  intro r
  induction r with
  | zero =>
    intro S _ _ hS
    simp only [T] at hS
    rw [pow_zero, Finset.one_le_card]
    obtain ⟨f, hf⟩ := Finset.card_pos.1 hS
    refine ⟨(∅, fun _ => 0), ?_⟩
    rw [mem_Sh]
    refine ⟨fun _ _ => rfl, fun i hi => by simp at hi, fun _ => ⟨f, hf, fun i hi => by simp at hi⟩⟩
  | succ r ih =>
    intro S hB hsep hS
    have hT : K * (T K r - 1) < S.card - 1 := by
      cases r with
      | zero => simp only [T, pow_zero] at hS ⊢; omega
      | succ r =>
        simp only [T] at hS ⊢
        have hP : 1 ≤ K^r := Nat.one_le_pow _ _ (by omega)
        have hQ : K ≤ K^r * K := by nlinarith
        rw [pow_succ] at hS
        have e : K * (2 * K^r - 1) = 2 * (K^r * K) - K := by
          rw [Nat.mul_sub_one]; congr 1; ring
        rw [e]; omega
    obtain ⟨i, j1, j2, hj, h1, h2, hjB⟩ := pigeon S hB hsep hK hT
    have e1 := ih (S.filter (fun h => h i = j1)) (fun h hh => hB h (Finset.mem_filter.1 hh).1)
      (fun f hf g hg => hsep f (Finset.mem_filter.1 hf).1 g (Finset.mem_filter.1 hg).1) h1
    have e2 := ih (S.filter (fun h => h i = j2)) (fun h hh => hB h (Finset.mem_filter.1 hh).1)
      (fun f hf g hg => hsep f (Finset.mem_filter.1 hf).1 g (Finset.mem_filter.1 hg).1) h2
    have := step_card (B := B) (S := S) (F1 := S.filter (fun h => h i = j1))
      (F2 := S.filter (fun h => h i = j2)) (fun h hh => (Finset.mem_filter.1 hh).2)
      (fun h hh => (Finset.mem_filter.1 hh).2) hj hjB
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    rw [pow_succ]; omega

end L20dd4c

namespace L20dd4c

open Classical

noncomputable def V (B d m : ℕ) : Finset (Finset (Fin m) × (Fin m → ℕ)) :=
  ((Finset.univ : Finset (Finset (Fin m))) ×ˢ
      Fintype.piFinset (fun _ : Fin m => Finset.range (B+1))).filter
   (fun p => (∀ i, i ∉ p.1 → p.2 i = 0) ∧ (∀ i ∈ p.1, p.2 i + 2 ≤ B) ∧ p.1.card ≤ d)

lemma V_card_nat (B d m : ℕ) :
    (V B d m).card ≤ ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card ≤ d),
      B ^ A.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card ≤ d))]
  · apply Finset.sum_le_sum
    intro A _
    calc ((V B d m).filter (fun a => a.1 = A)).card
        ≤ (Fintype.piFinset (fun i : Fin m => if i ∈ A then Finset.range B else {0})).card := by
          apply Finset.card_le_card_of_injOn Prod.snd
          · intro a ha
            simp only [Finset.mem_coe, Finset.mem_filter, V] at ha
            obtain ⟨⟨_, h1, h2, _⟩, rfl⟩ := ha
            simp only [Finset.mem_coe, Fintype.mem_piFinset]
            intro i
            split_ifs with hi
            · have := h2 i hi; simp only [Finset.mem_range]; omega
            · simp [h1 i hi]
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
            exact Prod.ext (ha.2.trans hb.2.symm) hab
      _ = B ^ A.card := by
          rw [Fintype.card_piFinset]
          have : ∀ i : Fin m, ((if i ∈ A then Finset.range B else {0}) : Finset ℕ).card =
              if i ∈ A then B else 1 := fun i => by split_ifs <;> simp
          simp_rw [this]
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · intro a ha
    simp only [Finset.mem_coe, V, Finset.mem_filter] at ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha.2.2.2

lemma V_zero_card (B m : ℕ) : (V B 0 m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [V, Finset.mem_filter, Nat.le_zero, Finset.card_eq_zero] at ha hb
  refine Prod.ext (ha.2.2.2.trans hb.2.2.2.symm) (funext fun i => ?_)
  rw [ha.2.1 i (by rw [ha.2.2.2]; simp), hb.2.1 i (by rw [hb.2.2.2]; simp)]

lemma V_card_real (B d m : ℕ) (hB : 1 ≤ B) (hd : 1 ≤ d) (hdm : d ≤ m) :
    ((V B d m).card : ℝ) ≤ ((B : ℝ) * Real.exp 1 * m / d) ^ d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hq0 : (0 : ℝ) ≤ (d : ℝ) / m := by positivity
  have hq1 : (d : ℝ) / m ≤ 1 := by
    rw [div_le_one hm']; exact_mod_cast hdm
  have step1 : ((V B d m).card : ℝ) ≤
      ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card ≤ d),
        ((B : ℝ) ^ A.card) := by
    exact_mod_cast V_card_nat B d m
  have step2 : ∀ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card ≤ d),
      ((B : ℝ) ^ A.card) ≤ (B : ℝ) ^ d * ((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ A.card := by
    intro A hA
    simp only [Finset.mem_filter] at hA
    have a1 : (B : ℝ) ^ A.card ≤ (B : ℝ) ^ d := pow_le_pow_right₀ hB' hA.2
    have a2 : ((d : ℝ) / m) ^ d ≤ ((d : ℝ) / m) ^ A.card := pow_le_pow_of_le_one hq0 hq1 hA.2
    have a3 : 1 ≤ ((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ A.card := by
      calc (1 : ℝ) = ((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ d := by
            rw [← mul_pow]; field_simp; simp
        _ ≤ _ := by gcongr
    calc (B : ℝ) ^ A.card ≤ (B : ℝ) ^ d := a1
      _ = (B : ℝ) ^ d * 1 := by ring
      _ ≤ (B : ℝ) ^ d * (((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ A.card) := by gcongr
      _ = _ := by ring
  have step3 : ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card ≤ d),
        ((B : ℝ) ^ d * ((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ A.card) ≤
      ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))),
        ((B : ℝ) ^ d * ((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ A.card) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have step4 : ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))), ((d : ℝ) / m) ^ A.card =
      (1 + (d : ℝ) / m) ^ m := by
    rw [← Finset.powerset_univ]
    have := Finset.sum_pow_mul_eq_add_pow ((d : ℝ) / m) 1 (Finset.univ : Finset (Fin m))
    simp only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin] at this
    rw [this, add_comm]
  have step5 : (1 + (d : ℝ) / m) ^ m ≤ Real.exp 1 ^ d := by
    calc (1 + (d : ℝ) / m) ^ m ≤ (Real.exp ((d : ℝ) / m)) ^ m := by
          gcongr
          linarith [Real.add_one_le_exp ((d : ℝ) / m)]
      _ = Real.exp 1 ^ d := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1; field_simp
  calc ((V B d m).card : ℝ) ≤ _ := step1
    _ ≤ _ := Finset.sum_le_sum step2
    _ ≤ _ := step3
    _ = (B : ℝ) ^ d * ((m : ℝ) / d) ^ d *
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))), ((d : ℝ) / m) ^ A.card := by
        rw [Finset.mul_sum]
    _ ≤ (B : ℝ) ^ d * ((m : ℝ) / d) ^ d * Real.exp 1 ^ d := by
        rw [step4]; gcongr
    _ = _ := by
        rw [div_pow, div_pow, mul_pow, mul_pow]; field_simp

end L20dd4c

namespace L20dd4c

open Classical BartlettNN.Margin BartlettNN.FatNet

noncomputable def qv {X : Type*} {m : ℕ} (M γ : ℝ) (x : Fin m → X) (f : X → ℝ) : Fin m → ℕ :=
  fun i => ⌊(f (x i) + M / 2) / (γ / 2)⌋₊

lemma qv_le {X : Type*} {m : ℕ} {M γ : ℝ} (hγ : 0 < γ) (x : Fin m → X) {f : X → ℝ}
    (hf : ∀ y, f y ∈ Set.Icc (-M / 2) (M / 2)) (i : Fin m) : qv M γ x f i ≤ ⌊2 * M / γ⌋₊ := by
  unfold qv
  apply Nat.floor_le_floor
  have h1 := (hf (x i)).2
  rw [div_le_iff₀ (by positivity : (0:ℝ) < γ / 2)]
  have : 2 * M / γ * (γ / 2) = M := by field_simp
  rw [this]; linarith

lemma floor_sep {M γ a b : ℝ} (hγ : 0 < γ) (ha : -M / 2 ≤ a) (hab : a + γ ≤ b) :
    ⌊(a + M / 2) / (γ / 2)⌋₊ + 2 ≤ ⌊(b + M / 2) / (γ / 2)⌋₊ := by
  apply Nat.le_floor
  have h0 : 0 ≤ (a + M / 2) / (γ / 2) := div_nonneg (by linarith) (by linarith)
  have h1 := Nat.floor_le h0
  have e : (b + M / 2) / (γ / 2) = (a + M / 2) / (γ / 2) + (b - a) / (γ / 2) := by ring
  have h2 : 2 ≤ (b - a) / (γ / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  push_cast
  linarith

lemma qv_sep {X : Type*} {m : ℕ} {M γ : ℝ} (hγ : 0 < γ) (x : Fin m → X) {f g : X → ℝ}
    (hf : ∀ y, f y ∈ Set.Icc (-M / 2) (M / 2)) (hg : ∀ y, g y ∈ Set.Icc (-M / 2) (M / 2))
    (i : Fin m) (h : γ ≤ |f (x i) - g (x i)|) :
    qv M γ x f i + 2 ≤ qv M γ x g i ∨ qv M γ x g i + 2 ≤ qv M γ x f i := by
  unfold qv
  rcases le_abs'.mp h with h' | h'
  · left; exact floor_sep hγ (hf (x i)).1 (by linarith)
  · right; exact floor_sep hγ (hg (x i)).1 (by linarith)

lemma exists_sep {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (h : γ ≤ dInf x f g) : ∃ i, γ ≤ |f (x i) - g (x i)| := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exfalso; unfold dInf at h; rw [Real.iSup_of_isEmpty] at h; linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => |f (x i) - g (x i)|)
    refine ⟨i, ?_⟩
    unfold dInf at h
    rw [← hi] at h
    exact h

lemma dInf_comm {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) :
    dInf x f g = dInf x g f := by
  unfold dInf
  congr 1; funext i; exact abs_sub_comm _ _

lemma dL2_le_dInf {X : Type*} {m : ℕ} (hm : 0 < m) (x : Fin m → X) (f g : X → ℝ) :
    dL2 x f g ≤ dInf x f g := by
  have hD : ∀ i, |f (x i) - g (x i)| ≤ dInf x f g := fun i =>
    le_ciSup (f := fun i => |f (x i) - g (x i)|) (Finite.bddAbove_range _) i
  have hD0 : 0 ≤ dInf x f g := (abs_nonneg _).trans (hD ⟨0, hm⟩)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have h1 : ∀ i, (f (x i) - g (x i)) ^ 2 ≤ (dInf x f g) ^ 2 := fun i => by
    rw [← sq_abs]; gcongr; exact hD i
  have h2 : (1 / (m : ℝ)) * ∑ i, (f (x i) - g (x i)) ^ 2 ≤ (dInf x f g) ^ 2 := by
    calc (1 / (m : ℝ)) * ∑ i, (f (x i) - g (x i)) ^ 2
        ≤ (1 / (m : ℝ)) * ∑ _i : Fin m, (dInf x f g) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h1 i) (by positivity)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  unfold dL2
  calc Real.sqrt _ ≤ Real.sqrt ((dInf x f g) ^ 2) := Real.sqrt_le_sqrt h2
    _ = _ := Real.sqrt_sq hD0

lemma bridge {X : Type*} {m : ℕ} {F : Set (X → ℝ)} {M γ : ℝ} {d : ℕ} (hγ : 0 < γ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : fat F (γ / 4) = d) (x : Fin m → X) (P : Finset (X → ℝ))
    (hP : (P : Set (X → ℝ)) ⊆ F)
    {B : ℕ} {p : Finset (Fin m) × (Fin m → ℕ)} (hp : p ∈ Sh B (P.image (qv M γ x))) :
    p.1.card ≤ d := by
  rw [mem_Sh] at hp
  obtain ⟨_, _, h3⟩ := hp
  set e := p.1.orderEmbOfFin rfl with he_def
  have he : ∀ j, e j ∈ p.1 := fun j => p.1.orderEmbOfFin_mem rfl j
  have hinj : Function.Injective e := e.injective
  have hGS : GammaShatters F (γ / 4) (x ∘ e) := by
    refine ⟨fun j => γ / 2 * ((p.2 (e j) : ℝ) + 3 / 2) - M / 2, fun b => ?_⟩
    obtain ⟨h, hh, hh'⟩ := h3 (Function.extend e b (fun _ => true))
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hh
    refine ⟨f, hP hf, fun j => ?_⟩
    have hc : Function.extend e b (fun _ => true) (e j) = b j := hinj.extend_apply b _ j
    have key := hh' (e j) (he j)
    rw [hc] at key
    have hfx := hF f (hP hf) (x (e j))
    set t := (f (x (e j)) + M / 2) / (γ / 2) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hfx.1]) (by linarith)
    have hft : f (x (e j)) = t * (γ / 2) - M / 2 := by rw [ht]; field_simp; ring
    simp only [Function.comp_apply]
    rw [hft]
    cases hb : b j
    · have h1 := key.2 hb
      have h2 : t < (qv M γ x f (e j) : ℝ) + 1 := Nat.lt_floor_add_one t
      have h3' : (qv M γ x f (e j) : ℝ) ≤ p.2 (e j) := by exact_mod_cast h1
      simp only [pm, Bool.false_eq_true, if_false]
      nlinarith [mul_pos hγ (show (0:ℝ) < p.2 (e j) + 1 - t by linarith)]
    · have h1 := key.1 hb
      have h2 : (qv M γ x f (e j) : ℝ) ≤ t := Nat.floor_le ht0
      have h3' : (p.2 (e j) : ℝ) + 2 ≤ qv M γ x f (e j) := by exact_mod_cast h1
      simp only [pm, if_true]
      nlinarith [mul_nonneg hγ.le (show (0:ℝ) ≤ t - p.2 (e j) - 2 by linarith)]
  have hk : (p.1.card : ℕ∞) ≤ fat F (γ / 4) := by
    unfold fat
    exact le_iSup_of_le p.1.card (le_iSup_of_le (x ∘ e) (le_iSup_of_le hGS le_rfl))
  rw [hd] at hk
  exact_mod_cast hk

noncomputable def cc (M γ : ℝ) (d m : ℕ) : ℕ :=
  T (m * (⌊2 * M / γ⌋₊ + 1) ^ 2) (Nat.log 2 (V ⌊2 * M / γ⌋₊ d m).card + 1)

lemma packing_bound {X : Type*} {m : ℕ} {F : Set (X → ℝ)} {M γ : ℝ} {d : ℕ} (hγ : 0 < γ)
    (hm : 0 < m) (hγM : γ ≤ M)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : fat F (γ / 4) = d) (x : Fin m → X) (P : Finset (X → ℝ))
    (hP : (P : Set (X → ℝ)) ⊆ F)
    (hsep : ∀ f ∈ P, ∀ g ∈ P, f ≠ g → γ ≤ dInf x f g) :
    P.card < cc M γ d m := by
  unfold cc
  set B := ⌊2 * M / γ⌋₊ with hBdef
  set K := m * (B + 1) ^ 2 with hKdef
  set Y := (V B d m).card with hY
  have hB2 : 2 ≤ B := Nat.le_floor (by push_cast; rw [le_div_iff₀ hγ]; linarith)
  have hK2 : 2 ≤ K := by
    have : 9 ≤ (B + 1) ^ 2 := by nlinarith
    calc 2 ≤ 1 * 9 := by norm_num
      _ ≤ m * (B + 1) ^ 2 := Nat.mul_le_mul hm this
  have hinj : Set.InjOn (qv M γ x) (P : Set (X → ℝ)) := by
    intro f hf g hg hfg
    by_contra hne
    obtain ⟨i, hi⟩ := exists_sep x f g hγ (hsep f hf g hg hne)
    have := qv_sep hγ x (hF f (hP hf)) (hF g (hP hg)) i hi
    rw [hfg] at this; omega
  have hQc : (P.image (qv M γ x)).card = P.card := Finset.card_image_of_injOn hinj
  have hQB : ∀ h ∈ P.image (qv M γ x), ∀ i, h i ≤ B := by
    intro h hh i
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hh
    exact qv_le hγ x (hF f (hP hf)) i
  have hQsep : ∀ f ∈ P.image (qv M γ x), ∀ g ∈ P.image (qv M γ x), f ≠ g →
      ∃ i, f i + 2 ≤ g i ∨ g i + 2 ≤ f i := by
    intro f hf g hg hfg
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hg
    have hne : f' ≠ g' := fun h => hfg (h ▸ rfl)
    obtain ⟨i, hi⟩ := exists_sep x f' g' hγ (hsep f' hf' g' hg' hne)
    exact ⟨i, qv_sep hγ x (hF f' (hP hf')) (hF g' (hP hg')) i hi⟩
  have hShV : Sh B (P.image (qv M γ x)) ⊆ V B d m := by
    intro p hp
    have hc := bridge hγ hF hd x P hP hp
    rw [mem_Sh] at hp
    simp only [V, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => ?_, hp.1, hp.2.1, hc⟩
    by_cases hi : i ∈ p.1
    · have := hp.2.1 i hi; omega
    · rw [hp.1 i hi]; omega
  by_contra hcon
  rw [not_lt, ← hQc] at hcon
  have h1 := core (le_refl K) hK2 _ _ hQB hQsep hcon
  have h2 := Finset.card_le_card hShV
  have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Y
  rw [Nat.succ_eq_add_one] at h3
  rw [← hY] at h2
  omega

lemma cover_bound {X : Type*} {m : ℕ} {F : Set (X → ℝ)} {M γ : ℝ} {d : ℕ} (hγ : 0 < γ)
    (hm : 0 < m) (hγM : γ ≤ M)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : fat F (γ / 4) = d) (x : Fin m → X) :
    coverNum (dL2 x) F γ ≤ ((cc M γ d m - 1 : ℕ) : ℕ∞) := by
  set Spk : Set ℕ := {k | ∃ P : Finset (X → ℝ), (P : Set (X → ℝ)) ⊆ F ∧
    (∀ f ∈ P, ∀ g ∈ P, f ≠ g → γ ≤ dInf x f g) ∧ P.card = k} with hSpk
  have hne : Spk.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hbdd : BddAbove Spk := by
    refine ⟨cc M γ d m, ?_⟩
    rintro k ⟨P, hP, hs, rfl⟩
    exact (packing_bound hγ hm hγM hF hd x P hP hs).le
  obtain ⟨P, hP, hs, hcard⟩ := Nat.sSup_mem hne hbdd
  have hcov : ∀ f ∈ F, ∃ g ∈ P, dL2 x g f < γ := by
    intro f hf
    by_contra hcon
    push_neg at hcon
    have hfP : f ∉ P := by
      intro hfP
      have h1 := hcon f hfP
      have h2 : dL2 x f f = 0 := by simp [dL2]
      linarith
    have hs' : ∀ a ∈ insert f P, ∀ b ∈ insert f P, a ≠ b → γ ≤ dInf x a b := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, dInf_comm]; exact (hcon b hb).trans (dL2_le_dInf hm x b f)
      · rw [hb]; exact (hcon a ha).trans (dL2_le_dInf hm x a f)
      · exact hs a ha b hb hab
    have hmem : (insert f P).card ∈ Spk :=
      ⟨insert f P, by rw [Finset.coe_insert]; exact Set.insert_subset hf hP, hs', rfl⟩
    have := le_csSup hbdd hmem
    rw [Finset.card_insert_of_notMem hfP, hcard] at this
    omega
  have hPc := packing_bound hγ hm hγM hF hd x P hP hs
  unfold coverNum
  calc _ ≤ (P.card : ℕ∞) := iInf₂_le P hcov
    _ ≤ _ := by exact_mod_cast (show P.card ≤ cc M γ d m - 1 by omega)

lemma N2_le_one {X : Type*} {F : Set (X → ℝ)} {M γ : ℝ} {m : ℕ} (hγM : M < γ) (hM : 0 < M)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) : N2 F γ m ≤ 1 := by
  apply iSup_le
  intro x
  unfold coverNum
  have hm1 : (1 / (m : ℝ)) * m ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · have : (m : ℝ) ≠ 0 := by positivity
      field_simp; rfl
  have hcov : ∀ f ∈ F, ∃ g ∈ ({0} : Finset (X → ℝ)), dL2 x g f < γ := by
    intro f hf
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    have hterm : ∀ i, ((0 : X → ℝ) (x i) - f (x i)) ^ 2 ≤ (M / 2) ^ 2 := by
      intro i
      have := hF f hf (x i)
      simp only [Pi.zero_apply, zero_sub, neg_sq]
      nlinarith [this.1, this.2]
    have hsum : (1 / (m : ℝ)) * ∑ i, ((0 : X → ℝ) (x i) - f (x i)) ^ 2 ≤ (M / 2) ^ 2 := by
      calc _ ≤ (1 / (m : ℝ)) * ∑ _i : Fin m, (M / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
        _ = ((1 / (m : ℝ)) * m) * (M / 2) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ 1 * (M / 2) ^ 2 := by gcongr
        _ = _ := one_mul _
    have : dL2 x 0 f ≤ M / 2 := by
      calc dL2 x 0 f = Real.sqrt ((1 / (m : ℝ)) * ∑ i, ((0 : X → ℝ) (x i) - f (x i)) ^ 2) := rfl
        _ ≤ Real.sqrt ((M / 2) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = M / 2 := Real.sqrt_sq (by linarith)
    linarith
  calc _ ≤ (({0} : Finset (X → ℝ)).card : ℕ∞) := iInf₂_le _ hcov
    _ = 1 := by simp

lemma gamma_le_two_M {X : Type*} {F : Set (X → ℝ)} {M γ : ℝ} {d : ℕ}
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : fat F (γ / 4) = d) (hd1 : 1 ≤ d) : γ ≤ 2 * M := by
  by_contra hlt
  push_neg at hlt
  have hfat : fat F (γ / 4) ≤ 0 := by
    unfold fat
    refine iSup_le fun k => iSup_le fun x => iSup_le fun hGS => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · exfalso
      obtain ⟨r, hr⟩ := hGS
      obtain ⟨h1, hh1, e1⟩ := hr (fun _ => true)
      obtain ⟨h2, hh2, e2⟩ := hr (fun _ => false)
      have a1 := e1 ⟨0, hk⟩
      have a2 := e2 ⟨0, hk⟩
      simp [pm] at a1 a2
      have b1 := hF h1 hh1 (x ⟨0, hk⟩)
      have b2 := hF h2 hh2 (x ⟨0, hk⟩)
      simp only [Set.mem_Icc] at b1 b2
      linarith [b1.2, b2.1]
  rw [hd] at hfat
  have : d = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hfat
  omega

lemma V_pos (B d m : ℕ) : 0 < (V B d m).card :=
  Finset.card_pos.2 ⟨(∅, fun _ => 0), by simp [V]⟩

end L20dd4c

open BartlettNN.FatNet in
theorem solution {X : Type*} (F : Set (X → ℝ)) (M γ : ℝ) (d m : ℕ)
    (hM : 0 < M) (hγ : 0 < γ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : BartlettNN.Margin.fat F (γ / 4) = d)
    (hm : 2 + 2 * (d : ℝ) * Real.logb 2 (32 * M / γ) ≤ (m : ℝ)) :
    ∃ N : ℕ, N2 F γ m = N ∧
      Real.logb 2 N < 1 + (d : ℝ) * Real.logb 2 (4 * Real.exp 1 * m * M / (d * γ)) *
        Real.logb 2 (9 * m * M ^ 2 / γ ^ 2) := by
  set L1 := Real.logb 2 (4 * Real.exp 1 * m * M / (d * γ)) with hL1
  set L2 := Real.logb 2 (9 * m * M ^ 2 / γ ^ 2) with hL2
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- nonnegativity of the product term
  have hpos : 0 ≤ (d : ℝ) * L1 * L2 := by
    rcases Nat.eq_zero_or_pos d with h0 | hd1
    · simp [h0]
    · have h2M := L20dd4c.gamma_le_two_M hF hd hd1
      have hlog4 : 4 ≤ Real.logb 2 (32 * M / γ) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
        rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [le_div_iff₀ hγ]; nlinarith
      have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have hm8 : 8 * (d : ℝ) + 2 ≤ m := by nlinarith
      have hA : 0 ≤ L1 := by
        apply Real.logb_nonneg (by norm_num)
        rw [one_le_div (by positivity)]
        have hMm : 0 ≤ (m : ℝ) * M := by positivity
        calc (d : ℝ) * γ ≤ d * (2 * M) := by gcongr
          _ ≤ m * M := by nlinarith
          _ ≤ 4 * Real.exp 1 * m * M := by nlinarith
      have hB : 0 ≤ L2 := by
        apply Real.logb_nonneg (by norm_num)
        rw [one_le_div (by positivity)]
        have : γ ^ 2 ≤ 4 * M ^ 2 := by nlinarith
        nlinarith
      exact mul_nonneg (mul_nonneg hd0 hA) hB
  by_cases hγM : γ ≤ M
  · -- main case
    have hlog5 : 5 ≤ Real.logb 2 (32 * M / γ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [le_div_iff₀ hγ]; nlinarith
    have hm10 : 10 * (d : ℝ) + 2 ≤ m := by nlinarith
    have hmpos : 0 < m := by
      have : (0 : ℝ) < m := by linarith
      exact_mod_cast this
    have hdm : d ≤ m := by
      have : (d : ℝ) ≤ m := by linarith
      exact_mod_cast this
    have hc : N2 F γ m ≤ ((L20dd4c.cc M γ d m - 1 : ℕ) : ℕ∞) :=
      iSup_le fun x => L20dd4c.cover_bound hγ hmpos hγM hF hd x
    have hne : N2 F γ m ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc
    refine ⟨(N2 F γ m).toNat, (ENat.coe_toNat hne).symm, ?_⟩
    have hN : (N2 F γ m).toNat ≤ L20dd4c.cc M γ d m - 1 := by
      have : ((N2 F γ m).toNat : ℕ∞) ≤ ((L20dd4c.cc M γ d m - 1 : ℕ) : ℕ∞) := by
        rw [ENat.coe_toNat hne]; exact hc
      exact_mod_cast this
    set N := (N2 F γ m).toNat with hNdef
    set B := ⌊2 * M / γ⌋₊ with hBdef
    set K := m * (B + 1) ^ 2 with hKdef
    set Y := (L20dd4c.V B d m).card with hYdef
    set r := Nat.log 2 Y with hr
    have hcc : L20dd4c.cc M γ d m = 2 * K ^ r := by
      unfold L20dd4c.cc; rfl
    rw [hcc] at hN
    have hK1 : 1 ≤ K := by
      have : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc 1 = 1 * 1 := by norm_num
        _ ≤ m * (B + 1) ^ 2 := Nat.mul_le_mul hmpos this
    have hKr : 1 ≤ K ^ r := Nat.one_le_pow _ _ (by omega)
    have hN1 : N + 1 ≤ 2 * K ^ r := by omega
    have hN1r : (N : ℝ) + 1 ≤ 2 * (K : ℝ) ^ r := by exact_mod_cast hN1
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    -- bound on log2 K
    have hBle : (B : ℝ) ≤ 2 * M / γ := Nat.floor_le (by positivity)
    have hMg : 1 ≤ M / γ := by rw [le_div_iff₀ hγ]; linarith
    have hB1 : (B : ℝ) + 1 ≤ 3 * M / γ := by
      have : 3 * M / γ = 2 * M / γ + M / γ := by ring
      linarith
    have hKle : (K : ℝ) ≤ 9 * m * M ^ 2 / γ ^ 2 := by
      have : (K : ℝ) = m * ((B : ℝ) + 1) ^ 2 := by simp [hKdef]
      rw [this]
      calc (m : ℝ) * ((B : ℝ) + 1) ^ 2 ≤ m * (3 * M / γ) ^ 2 := by
            gcongr
        _ = 9 * m * M ^ 2 / γ ^ 2 := by ring
    have hlogK : Real.logb 2 K ≤ L2 := Real.logb_le_logb_of_le (by norm_num) hKpos hKle
    have hlogK0 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) (by exact_mod_cast hK1)
    -- bound on log2 Y
    have hY0 : 0 < Y := L20dd4c.V_pos B d m
    have hYr : (0 : ℝ) < Y := by exact_mod_cast hY0
    have hlogY0 : 0 ≤ Real.logb 2 Y :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hY0)
    have hrY : (r : ℝ) ≤ Real.logb 2 Y := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hYr, Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 hY0.ne'
    have hlogY : Real.logb 2 Y ≤ d * L1 := by
      rcases Nat.eq_zero_or_pos d with h0 | hd1
      · have hY1 : Y ≤ 1 := by
          rw [hYdef, h0]; exact L20dd4c.V_zero_card B m
        have : (Y : ℝ) ≤ 1 := by exact_mod_cast hY1
        have : Real.logb 2 Y ≤ 0 := Real.logb_nonpos (by norm_num) hYr.le this
        simp [h0]; linarith
      · have hB1' : 1 ≤ B := by
          have : 2 ≤ B := Nat.le_floor (by push_cast; rw [le_div_iff₀ hγ]; linarith)
          omega
        have hcnt := L20dd4c.V_card_real B d m hB1' hd1 hdm
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd1
        have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1'
        have hbase : 0 < (B : ℝ) * Real.exp 1 * m / d := by positivity
        calc Real.logb 2 Y ≤ Real.logb 2 (((B : ℝ) * Real.exp 1 * m / d) ^ d) :=
              Real.logb_le_logb_of_le (by norm_num) hYr hcnt
          _ = d * Real.logb 2 ((B : ℝ) * Real.exp 1 * m / d) := by rw [Real.logb_pow]
          _ ≤ d * L1 := by
              apply mul_le_mul_of_nonneg_left _ hd0
              rw [hL1]
              apply Real.logb_le_logb_of_le (by norm_num) hbase
              calc (B : ℝ) * Real.exp 1 * m / d ≤ (4 * M / γ) * Real.exp 1 * m / d := by
                    gcongr
                    calc (B : ℝ) ≤ 2 * M / γ := hBle
                      _ ≤ 4 * M / γ := by gcongr; norm_num
                _ = 4 * Real.exp 1 * m * M / (d * γ) := by ring
    have hprod : (r : ℝ) * Real.logb 2 K ≤ d * L1 * L2 := by
      calc (r : ℝ) * Real.logb 2 K ≤ Real.logb 2 Y * Real.logb 2 K :=
            mul_le_mul_of_nonneg_right hrY hlogK0
        _ ≤ Real.logb 2 Y * L2 := mul_le_mul_of_nonneg_left hlogK hlogY0
        _ ≤ d * L1 * L2 := by
            apply mul_le_mul_of_nonneg_right hlogY
            exact hlogK0.trans hlogK
    rcases Nat.eq_zero_or_pos N with h0 | hNpos
    · rw [h0]; simp; linarith
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hlt : Real.logb 2 N < Real.logb 2 (2 * (K : ℝ) ^ r) :=
        Real.logb_lt_logb (by norm_num) hNr (by linarith)
      have heq : Real.logb 2 (2 * (K : ℝ) ^ r) = 1 + r * Real.logb 2 K := by
        rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
          Real.logb_pow]
      linarith
  · push_neg at hγM
    have h1 := L20dd4c.N2_le_one hγM hM hF (m := m)
    have hne : N2 F γ m ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
    refine ⟨(N2 F γ m).toNat, (ENat.coe_toNat hne).symm, ?_⟩
    have hN : (N2 F γ m).toNat ≤ 1 := by
      have : ((N2 F γ m).toNat : ℕ∞) ≤ 1 := by rw [ENat.coe_toNat hne]; exact h1
      exact_mod_cast this
    have : Real.logb 2 ((N2 F γ m).toNat : ℝ) ≤ 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hN with h | h <;> rw [h] <;> simp
    linarith
