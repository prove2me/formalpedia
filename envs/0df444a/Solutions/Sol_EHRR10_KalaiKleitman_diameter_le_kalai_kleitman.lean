-- Prove2me | solution 1 for EHRR10.KalaiKleitman.diameter_le_kalai_kleitman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:27:09.421988+00:00
-- url     : https://prove2.me/submissions/8c2b392d-2a2e-48b7-90a4-fa68480aca14

import Mathlib
import Definitions.Def_EHRR10_LowerBound_BaseAbstraction



namespace EHRR10.KalaiKleitman

open Classical

section CLFsec

variable {β : Type*}

structure KKCLF (d : ℕ) (W : Finset β) (k : ℕ) (L : ℕ → Finset β → Prop) : Prop where
  ne : ∀ i ≤ k, ∃ x, L i x
  card : ∀ i ≤ k, ∀ x, L i x → x.card = d
  sub : ∀ i ≤ k, ∀ x, L i x → x ⊆ W
  disj : ∀ i ≤ k, ∀ j ≤ k, ∀ x, L i x → L j x → i = j
  conn : ∀ S : Finset β, ∀ i j l, i ≤ j → j ≤ l → l ≤ k →
    (∃ x, L i x ∧ S ⊆ x) → (∃ x, L l x ∧ S ⊆ x) → ∃ x, L j x ∧ S ⊆ x

noncomputable def kkU (L : ℕ → Finset β → Prop) (W : Finset β) (j : ℕ) : Finset β :=
  W.filter (fun b => ∃ i ≤ j, ∃ x, L i x ∧ b ∈ x)

lemma kk_prefix {d : ℕ} {W : Finset β} {k : ℕ} {L : ℕ → Finset β → Prop}
    (hC : KKCLF d W k L) (j : ℕ) (hj : j ≤ k) : KKCLF d (kkU L W j) j L where
  ne i hi := hC.ne i (by omega)
  card i hi := hC.card i (by omega)
  sub i hi x hx := by
    intro b hb
    simp only [kkU, Finset.mem_filter]
    exact ⟨hC.sub i (by omega) x hx hb, i, hi, x, hx, hb⟩
  disj i hi j' hj' := hC.disj i (by omega) j' (by omega)
  conn S i j' l h1 h2 h3 := hC.conn S i j' l h1 h2 (by omega)

lemma kk_rev {d : ℕ} {W : Finset β} {k : ℕ} {L : ℕ → Finset β → Prop}
    (hC : KKCLF d W k L) : KKCLF d W k (fun i x => L (k - i) x) where
  ne i hi := hC.ne (k - i) (by omega)
  card i hi := hC.card (k - i) (by omega)
  sub i hi := hC.sub (k - i) (by omega)
  disj i hi j hj x h1 h2 := by
    have := hC.disj (k - i) (by omega) (k - j) (by omega) x h1 h2
    omega
  conn S i j l h1 h2 h3 hi hl := hC.conn S (k - l) (k - j) (k - i) (by omega) (by omega) (by omega) hl hi

lemma kk_restrict {d : ℕ} {W : Finset β} {k : ℕ} {L : ℕ → Finset β → Prop}
    (hC : KKCLF d W k L) (s : β) (a b p q : ℕ) (hab : a ≤ b) (hpa : p ≤ a) (hbq : b ≤ q)
    (hqk : q ≤ k) (hp : ∃ x, L p x ∧ s ∈ x) (hq : ∃ x, L q x ∧ s ∈ x) :
    KKCLF (d - 1) (W.erase s) (b - a)
      (fun i z => ∃ x, L (a + i) x ∧ s ∈ x ∧ z = x.erase s) where
  ne i hi := by
    obtain ⟨x, hx, hsx⟩ := hp
    obtain ⟨y, hy, hsy⟩ := hq
    obtain ⟨z, hz, hsz⟩ := hC.conn {s} p (a + i) q (by omega) (by omega) hqk
      ⟨x, hx, by simpa using hsx⟩ ⟨y, hy, by simpa using hsy⟩
    exact ⟨z.erase s, z, hz, by simpa using hsz, rfl⟩
  card i hi z := by
    rintro ⟨x, hx, hsx, rfl⟩
    rw [Finset.card_erase_of_mem hsx, hC.card (a + i) (by omega) x hx]
  sub i hi z := by
    rintro ⟨x, hx, hsx, rfl⟩
    exact Finset.erase_subset_erase s (hC.sub (a + i) (by omega) x hx)
  disj i hi j hj z := by
    rintro ⟨x, hx, hsx, rfl⟩ ⟨y, hy, hsy, hxy⟩
    have : x = y := by
      rw [← Finset.insert_erase hsx, ← Finset.insert_erase hsy, hxy]
    subst this
    have := hC.disj (a + i) (by omega) (a + j) (by omega) x hx hy
    omega
  conn S i j l h1 h2 h3 := by
    rintro ⟨z, ⟨x, hx, hsx, rfl⟩, hSz⟩ ⟨z', ⟨y, hy, hsy, rfl⟩, hSz'⟩
    have hx' : insert s S ⊆ x := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hsx
      · exact Finset.mem_of_mem_erase (hSz ht)
    have hy' : insert s S ⊆ y := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hsy
      · exact Finset.mem_of_mem_erase (hSz' ht)
    obtain ⟨w, hw, hSw⟩ := hC.conn (insert s S) (a + i) (a + j) (a + l) (by omega) (by omega)
      (by omega) ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    refine ⟨w.erase s, ⟨w, hw, hSw (Finset.mem_insert_self _ _), rfl⟩, ?_⟩
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase (hSz ht)
    exact Finset.mem_erase.2 ⟨hts, hSw (Finset.mem_insert_of_mem ht)⟩

lemma kk_count {d : ℕ} {W : Finset β} {k : ℕ} {L : ℕ → Finset β → Prop}
    (hC : KKCLF d W k L) : k + 1 ≤ W.card.choose d := by
  rw [← Finset.card_powersetCard]
  have hf : ∀ i ∈ Finset.range (k + 1), ∃ x, L i x := fun i hi =>
    hC.ne i (by simp at hi; omega)
  let f : ℕ → Finset β := fun i => if h : i ≤ k then Classical.choose (hC.ne i h) else ∅
  have hfL : ∀ i ≤ k, L i (f i) := fun i hi => by
    simp only [f, dif_pos hi]; exact Classical.choose_spec (hC.ne i hi)
  have := Finset.card_le_card_of_injOn f (s := Finset.range (k + 1)) (t := W.powersetCard d)
    (by
      intro i hi
      have hi' : i ≤ k := by simp at hi; omega
      try simp only [Finset.mem_coe]
      exact Finset.mem_powersetCard.2 ⟨hC.sub i hi' _ (hfL i hi'), hC.card i hi' _ (hfL i hi')⟩)
    (by
      intro i hi j hj hij
      have hi' : i ≤ k := by simp at hi; omega
      have hj' : j ≤ k := by simp at hj; omega
      exact hC.disj i hi' j hj' (f i) (hfL i hi') (by rw [hij]; exact hfL j hj'))
  simpa using this

lemma kk_first_big {d : ℕ} {W : Finset β} {k : ℕ} {L : ℕ → Finset β → Prop}
    (hC : KKCLF d W k L) (h : ℕ) (F : ℝ) (hF : 0 ≤ F)
    (IH : ∀ (W' : Finset β) (k' : ℕ), KKCLF d W' k' L → W'.card ≤ h → (k' : ℝ) ≤ F) :
    (k : ℝ) ≤ F ∨ ∃ j ≤ k, (j : ℝ) ≤ F + 1 ∧ h < (kkU L W j).card := by
  by_cases hk : (kkU L W k).card ≤ h
  · exact Or.inl (IH _ k (kk_prefix hC k le_rfl) hk)
  right
  have ex : ∃ j, h < (kkU L W j).card := ⟨k, by omega⟩
  refine ⟨Nat.find ex, Nat.find_min' ex (by omega), ?_, Nat.find_spec ex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find ex) with h0 | h0
  · rw [h0]; simp; linarith
  · have hlt : Nat.pred (Nat.find ex) < Nat.find ex := by omega
    have hnot := Nat.find_min ex hlt
    have hle : Nat.find ex ≤ k := Nat.find_min' ex (by omega)
    have := IH _ _ (kk_prefix hC (Nat.pred (Nat.find ex)) (by omega)) (by omega)
    rw [h0]; push_cast; linarith


lemma kk_ineq (m d : ℕ) (hm : 3 ≤ m) (hd : 2 ≤ d) :
    2 * (((m / 2 : ℕ) : ℝ) ^ (1 + Real.logb 2 (d : ℝ)) + 1)
      + ((m - 1 : ℕ) : ℝ) ^ (1 + Real.logb 2 ((d - 1 : ℕ) : ℝ))
      ≤ (m : ℝ) ^ (1 + Real.logb 2 (d : ℝ)) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hhalf : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (Nat.div_mul_le_self m 2)
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hm1, hd1]
  set u := Real.logb 2 (d : ℝ) with hu_def
  have hu0 : 0 ≤ u := Real.logb_nonneg (by norm_num) (by linarith)
  have h2u : (2 : ℝ) ^ u = d := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hF : ((m / 2 : ℕ) : ℝ) ^ (1 + u) ≤ (m : ℝ) ^ (1 + u) / (2 * d) := by
    calc ((m / 2 : ℕ) : ℝ) ^ (1 + u) ≤ ((m : ℝ) / 2) ^ (1 + u) :=
          Real.rpow_le_rpow (by positivity) hhalf (by linarith)
      _ = (m : ℝ) ^ (1 + u) / (2 * d) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_add (by norm_num : (0:ℝ) < 2),
            Real.rpow_one, h2u]
  have hmA : (m : ℝ) ^ (1 + u) = m * (m : ℝ) ^ u := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  rcases eq_or_lt_of_le hd with h2 | h3
  · subst h2
    have hu : u = 1 := by rw [hu_def]; norm_num
    have hG : ((m : ℝ) - 1) ^ (1 + Real.logb 2 ((2 : ℕ) - 1 : ℝ)) = (m : ℝ) - 1 := by
      norm_num
    rw [hG]
    rw [hmA, hu, Real.rpow_one] at hF ⊢
    have : (m : ℝ) * m / (2 * ((2 : ℕ) : ℝ)) = m * m / 4 := by norm_num
    rw [this] at hF
    nlinarith
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h3
    set v := Real.logb 2 ((d : ℝ) - 1) with hv_def
    have h2v : (2 : ℝ) ^ v = d - 1 := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have hv1 : 1 ≤ v := by
      have : Real.logb 2 (2 : ℝ) ≤ v := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
      rwa [Real.logb_self_eq_one (by norm_num)] at this
    have huv : v ≤ u := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have hG : ((m : ℝ) - 1) ^ (1 + v) ≤ (m - 1) * (m : ℝ) ^ v := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
        (by linarith)
    set A := (m : ℝ) ^ u with hA
    set B := (m : ℝ) ^ v with hB
    have hAB : A = B * (m : ℝ) ^ (u - v) := by
      rw [hA, hB, ← Real.rpow_add (by linarith)]; ring_nf
    have hmuv : (d : ℝ) / (d - 1) ≤ (m : ℝ) ^ (u - v) := by
      have : (2 : ℝ) ^ (u - v) ≤ (m : ℝ) ^ (u - v) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
      rwa [Real.rpow_sub (by norm_num), h2u, h2v] at this
    have hB2 : (m : ℝ) ≤ B := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ m) hv1
      rwa [Real.rpow_one] at this
    have hBpos : 0 ≤ B := by linarith
    have hAB2 : B * d ≤ A * (d - 1) := by
      rw [hAB]
      have h := mul_le_mul_of_nonneg_left hmuv hBpos
      rw [mul_div_assoc'] at h
      rw [div_le_iff₀ (by linarith)] at h
      nlinarith
    rw [hmA] at hF ⊢
    have hF2 : ((m / 2 : ℕ) : ℝ) ^ (1 + u) * (2 * d) ≤ m * A := by
      rwa [le_div_iff₀ (by positivity)] at hF
    have hdpos : (0 : ℝ) < d := by linarith
    -- target: 2 * (F + 1) + G ≤ m * A
    have key : 2 * d + (m - 1) * B * d ≤ m * A * (d - 1) := by nlinarith
    have : 2 * (((m / 2 : ℕ) : ℝ) ^ (1 + u) + 1) * d + ((m : ℝ) - 1) ^ (1 + v) * d ≤ m * A * d := by
      nlinarith
    nlinarith

theorem kk_main (m : ℕ) : ∀ (d : ℕ), 1 ≤ d → ∀ (W : Finset β) (k : ℕ) (L : ℕ → Finset β → Prop),
    KKCLF d W k L → W.card ≤ m → (k : ℝ) ≤ (m : ℝ) ^ (1 + Real.logb 2 (d : ℝ)) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro d hd W k L hC hW
  have hcnt := kk_count hC
  rcases (by omega : d = 1 ∨ 2 ≤ d) with rfl | hd2
  · rw [Nat.choose_one_right] at hcnt
    simp only [Nat.cast_one, Real.logb_one, add_zero, Real.rpow_one]
    exact_mod_cast (by omega : k ≤ m)
  by_cases hm3 : m < 3
  · have hch : W.card.choose d ≤ 1 := by
      rcases lt_or_eq_of_le (by omega : W.card ≤ d) with h | h
      · rw [Nat.choose_eq_zero_of_lt h]; omega
      · rw [h, Nat.choose_self]
    have : k = 0 := by omega
    subst this
    simp only [Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have IHh : ∀ (W' : Finset β) (k' : ℕ) (L' : ℕ → Finset β → Prop), KKCLF d W' k' L' →
      W'.card ≤ m / 2 → (k' : ℝ) ≤ ((m / 2 : ℕ) : ℝ) ^ (1 + Real.logb 2 (d : ℝ)) :=
    fun W' k' L' h1 h2 => IH (m / 2) (by omega) d hd W' k' L' h1 h2
  have IHs : ∀ (W' : Finset β) (k' : ℕ) (L' : ℕ → Finset β → Prop), KKCLF (d - 1) W' k' L' →
      W'.card ≤ m - 1 → (k' : ℝ) ≤ ((m - 1 : ℕ) : ℝ) ^ (1 + Real.logb 2 ((d - 1 : ℕ) : ℝ)) :=
    fun W' k' L' h1 h2 => IH (m - 1) (by omega) (d - 1) (by omega) W' k' L' h1 h2
  have hineq := kk_ineq m d (by omega) hd2
  set F := ((m / 2 : ℕ) : ℝ) ^ (1 + Real.logb 2 (d : ℝ)) with hFdef
  set G := ((m - 1 : ℕ) : ℝ) ^ (1 + Real.logb 2 ((d - 1 : ℕ) : ℝ)) with hGdef
  have hF0 : 0 ≤ F := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hG0 : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases kk_first_big hC (m / 2) F hF0 (fun W' k' h1 h2 => IHh W' k' L h1 h2) with
    hk | ⟨j0, hj0k, hj0F, hj0U⟩
  · linarith
  rcases kk_first_big (kk_rev hC) (m / 2) F hF0 (fun W' k' h1 h2 => IHh W' k' _ h1 h2) with
    hk | ⟨j1, hj1k, hj1F, hj1U⟩
  · linarith
  by_cases hsum : k ≤ j0 + j1
  · have : (k : ℝ) ≤ j0 + j1 := by exact_mod_cast hsum
    linarith
  have hsub1 : kkU L W j0 ⊆ W := Finset.filter_subset _ _
  have hsub2 : kkU (fun i x => L (k - i) x) W j1 ⊆ W := Finset.filter_subset _ _
  have hcu := Finset.card_union_add_card_inter (kkU L W j0) (kkU (fun i x => L (k - i) x) W j1)
  have hcw := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
  have hne : (kkU L W j0 ∩ kkU (fun i x => L (k - i) x) W j1).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨s, hs⟩ := hne
  rw [Finset.mem_inter] at hs
  simp only [kkU, Finset.mem_filter] at hs
  obtain ⟨⟨hsW, i, hi, x, hx, hsx⟩, ⟨_, i', hi', y, hy, hsy⟩⟩ := hs
  have hR := kk_restrict hC s j0 (k - j1) i (k - i') (by omega) hi (by omega) (by omega)
    ⟨x, hx, hsx⟩ ⟨y, hy, hsy⟩
  have hWs : (W.erase s).card ≤ m - 1 := by rw [Finset.card_erase_of_mem hsW]; omega
  have hmid := IHs _ _ _ hR hWs
  have hkR : ((k - j1 - j0 : ℕ) : ℝ) = (k : ℝ) - j1 - j0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  linarith

end CLFsec

lemma kk_walk_ivt {α : Type*} {G : SimpleGraph α} (f : α → ℕ)
    (hf : ∀ a c, G.Adj a c → f c ≤ f a + 1) {a b : α} (q : G.Walk a b) :
    ∀ j : ℕ, f a ≤ j → j ≤ f b → ∃ w ∈ q.support, f w = j := by
  induction q with
  | @nil a => intro j h1 h2; exact ⟨a, by simp, by omega⟩
  | @cons a c b h q ih =>
    intro j h1 h2
    by_cases hj : j ≤ f a
    · exact ⟨a, by simp, by omega⟩
    · have := hf _ _ h
      obtain ⟨w, hw, hfw⟩ := ih j (by omega) h2
      exact ⟨w, by simp [hw], hfw⟩

theorem kk_core (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V)
    (hG : EHRR10.LowerBound.InB d n V G) (u v : V) :
    ∃ p : G.Walk u v, (p.length : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 d) := by
  obtain ⟨_, hcard, hcond⟩ := hG
  have : Nonempty V := ⟨u⟩
  have hconn : G.Connected := ⟨fun a b => (hcond a b).elim fun p _ => ⟨p⟩⟩
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  refine ⟨p, ?_⟩
  rw [hp]
  let L : ℕ → Finset (Fin n) → Prop := fun i x => ∃ hx : x ∈ V, G.dist u ⟨x, hx⟩ = i
  have hlip : ∀ a c : V, G.Adj a c → G.dist u c ≤ G.dist u a + 1 := by
    intro a c h
    have h1 := hconn.dist_triangle (u := u) (v := a) (w := c)
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h1
    exact h1
  have hconnL : ∀ S : Finset (Fin n), ∀ i j l, i ≤ j → j ≤ l → l ≤ G.dist u v →
      (∃ x, L i x ∧ S ⊆ x) → (∃ x, L l x ∧ S ⊆ x) → ∃ x, L j x ∧ S ⊆ x := by
    rintro S i j l h1 h2 _ ⟨x, ⟨hx, hdx⟩, hSx⟩ ⟨y, ⟨hy, hdy⟩, hSy⟩
    obtain ⟨q, hq⟩ := hcond ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨w, hw, hfw⟩ := kk_walk_ivt (fun w => G.dist u w) hlip q j (by omega)
      (by omega)
    refine ⟨w.1, ⟨w.2, hfw⟩, ?_⟩
    exact (Finset.subset_inter hSx hSy).trans (hq w hw)
  have hC : KKCLF d (Finset.univ : Finset (Fin n)) (G.dist u v) L :=
    { ne := by
        intro i hi
        obtain ⟨x, hx, -⟩ := hconnL ∅ 0 i (G.dist u v) (by omega) hi le_rfl
          ⟨u.1, ⟨u.2, by simp⟩, by simp⟩ ⟨v.1, ⟨v.2, rfl⟩, by simp⟩
        exact ⟨x, hx⟩
      card := by
        rintro i - x ⟨hx, -⟩
        exact hcard x hx
      sub := fun _ _ _ _ => Finset.subset_univ _
      disj := by
        rintro i - j - x ⟨hx, rfl⟩ ⟨hx', h⟩
        exact h
      conn := hconnL }
  have := kk_main n d hd _ _ L hC (by simp)
  exact this

end EHRR10.KalaiKleitman

open EHRR10.KalaiKleitman


theorem solution
    (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V)
    (hG : EHRR10.LowerBound.InB d n V G) (u v : V) :
    ∃ p : G.Walk u v, (p.length : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 d) := by
  exact kk_core d n hd V G hG u v
