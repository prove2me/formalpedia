-- Prove2me | solution 1 for DirS.sidorenko_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:58:19.276104+00:00
-- url     : https://prove2.me/submissions/0d620b2c-8b32-4d55-9f7b-3844f079d06d

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

noncomputable def g73u_hc {m n : ℕ} (H : BipGraph m n) {α β : Type*} (r : α → β → Prop) : ℕ :=
  Nat.card {f : (Fin m → α) × (Fin n → β) // ∀ i j, H.adj i j = true → r (f.1 i) (f.2 j)}

noncomputable def g73u_ec {α β : Type*} (r : α → β → Prop) : ℕ := Nat.card {p : α × β // r p.1 p.2}

lemma g73u_bipHomCount_eq {m n p q : ℕ} (H : BipGraph m n) (Q : BipGraph p q) :
    H.bipHomCount Q = g73u_hc H (fun x y => Q.adj x y = true) := by
  classical
  unfold BipGraph.bipHomCount g73u_hc
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro f _
  simp [List.all_eq_true, imp_iff_not_or]

lemma g73u_bipEdgeCount_eq {p q : ℕ} (Q : BipGraph p q) :
    Q.bipEdgeCount = g73u_ec (fun x y => Q.adj x y = true) := by
  classical
  unfold BipGraph.bipEdgeCount g73u_ec
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

lemma g73u_edgeCount_eq {N : ℕ} (G : OriGraph N) :
    G.edgeCount = g73u_ec (fun x y => G.edge x y = true) :=
  g73u_bipEdgeCount_eq (⟨G.edge⟩ : BipGraph N N)

lemma g73u_homCount_eq' {m N : ℕ} (B : OriGraph m) (G : OriGraph N) :
    B.homCount G = Nat.card {f : Fin m → Fin N // ∀ x y, B.edge x y = true → G.edge (f x) (f y) = true} := by
  classical
  unfold OriGraph.homCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro f _
  simp [List.all_eq_true, imp_iff_not_or]

lemma g73u_oe_cast {m n : ℕ} (H : BipGraph m n) (i : Fin m) (j : Fin n) :
    orientEdge m n H (Fin.castAdd n i) (Fin.natAdd m j) = H.adj i j := by
  unfold orientEdge
  rw [dif_pos ⟨by simp, by simp⟩]
  congr 1 <;> ext <;> simp

lemma g73u_oe_true {m n : ℕ} (H : BipGraph m n) (x y : Fin (m + n))
    (h : orientEdge m n H x y = true) :
    ∃ i j, x = Fin.castAdd n i ∧ y = Fin.natAdd m j ∧ H.adj i j = true := by
  unfold orientEdge at h
  split_ifs at h with hc
  have := y.isLt
  exact ⟨Fin.castLT x hc.1, ⟨y.val - m, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega), h⟩

def g73u_E (m n : ℕ) (X : Type*) : (Fin m → X) × (Fin n → X) ≃ (Fin (m + n) → X) where
  toFun g := Fin.append g.1 g.2
  invFun f := (fun i => f (Fin.castAdd n i), fun j => f (Fin.natAdd m j))
  left_inv g := by simp
  right_inv f := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp

lemma g73u_homCount_eq {m n N : ℕ} (H : BipGraph m n) (G : OriGraph N) :
    (orientOf H).homCount G = g73u_hc H (fun x y => G.edge x y = true) := by
  rw [g73u_homCount_eq']
  unfold g73u_hc
  refine Nat.card_congr (Equiv.subtypeEquiv (g73u_E m n (Fin N)) ?_).symm
  intro g
  constructor
  · intro h x y hxy
    obtain ⟨i, j, rfl, rfl, hij⟩ := g73u_oe_true H x y hxy
    simpa [g73u_E] using h i j hij
  · intro h i j hij
    have := h (Fin.castAdd n i) (Fin.natAdd m j) (by
      show orientEdge m n H _ _ = true
      rw [g73u_oe_cast]; exact hij)
    simpa [g73u_E] using this

lemma g73u_L1 {m n : ℕ} (H : BipGraph m n) : (orientOf H).edgeCount = H.bipEdgeCount := by
  rw [g73u_edgeCount_eq, g73u_bipEdgeCount_eq]
  unfold g73u_ec
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun q => ⟨(Fin.castAdd n q.1.1, Fin.natAdd m q.1.2), by
      show orientEdge m n H _ _ = true
      rw [g73u_oe_cast]; exact q.2⟩) ⟨?_, ?_⟩)
  · intro q q' h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.castAdd_inj, Fin.natAdd_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨p, hp⟩
    obtain ⟨i, j, h1, h2, h3⟩ := g73u_oe_true H p.1 p.2 hp
    exact ⟨⟨(i, j), h3⟩, Subtype.ext (Prod.ext h1.symm h2.symm)⟩

def g73u_fold {M : ℕ} (y : Fin (M + M)) : Fin M :=
  if h : y.val < M then ⟨y.val, h⟩ else ⟨y.val - M, by have := y.isLt; omega⟩

lemma g73u_fold_inj {M : ℕ} (y y' : Fin (M + M)) (h1 : decide (M ≤ y.val) = decide (M ≤ y'.val))
    (h2 : g73u_fold y = g73u_fold y') : y = y' := by
  unfold g73u_fold at h2
  have h2' := congrArg Fin.val h2
  apply Fin.ext
  split_ifs at h2' with ha hb hb <;> simp at h1 h2' <;> omega

lemma g73u_oe_Q {M : ℕ} (Q : BipGraph M M) (y z : Fin (M + M))
    (h : orientEdge M M Q y z = true) : Q.adj (g73u_fold y) (g73u_fold z) = true := by
  obtain ⟨i, j, rfl, rfl, hij⟩ := g73u_oe_true Q y z h
  have e1 : g73u_fold (Fin.castAdd M i) = i := by
    unfold g73u_fold; rw [dif_pos (by simp)]; rfl
  have e2 : g73u_fold (Fin.natAdd M j) = j := by
    unfold g73u_fold; rw [dif_neg (by simp)]; ext; simp
  rw [e1, e2]; exact hij

lemma g73u_hc_orient_le {m n M : ℕ} (H : BipGraph m n) (Q : BipGraph M M) :
    g73u_hc H (fun x y => (orientOf Q).edge x y = true) ≤
      2 ^ m * 2 ^ n * g73u_hc H (fun x y => Q.adj x y = true) := by
  unfold g73u_hc
  let φ : {f : (Fin m → Fin (M + M)) × (Fin n → Fin (M + M)) //
        ∀ i j, H.adj i j = true → (orientOf Q).edge (f.1 i) (f.2 j) = true} →
      ((Fin m → Bool) × (Fin n → Bool)) ×
        {f : (Fin m → Fin M) × (Fin n → Fin M) // ∀ i j, H.adj i j = true → Q.adj (f.1 i) (f.2 j) = true} :=
    fun f => ((fun i => decide (M ≤ (f.1.1 i).val), fun j => decide (M ≤ (f.1.2 j).val)),
      ⟨(fun i => g73u_fold (f.1.1 i), fun j => g73u_fold (f.1.2 j)),
        fun i j hij => g73u_oe_Q Q _ _ (f.2 i j hij)⟩)
  have hφ : Function.Injective φ := by
    intro f f' h
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact g73u_fold_inj _ _ (congrFun h1 i) (congrFun h3 i)
    · funext j
      exact g73u_fold_inj _ _ (congrFun h2 j) (congrFun h4 j)
  refine (Nat.card_le_card_of_injective φ hφ).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_prod]
  simp [Nat.card_eq_fintype_card]

lemma g73u_hc_pow {m n : ℕ} (H : BipGraph m n) {γ δ : Type*} (r : γ → δ → Prop) (k : ℕ) :
    g73u_hc H (fun (x : Fin k → γ) (y : Fin k → δ) => ∀ l, r (x l) (y l)) = (g73u_hc H r) ^ k := by
  unfold g73u_hc
  rw [show ∀ X : Type _, Nat.card X ^ k = Nat.card (Fin k → X) from fun X => by
    rw [Nat.card_fun, Nat.card_fin]]
  refine Nat.card_congr
    { toFun := fun f l => ⟨(fun i => f.1.1 i l, fun j => f.1.2 j l), fun i j h => f.2 i j h l⟩
      invFun := fun F => ⟨(fun i l => (F l).1.1 i, fun j l => (F l).1.2 j), fun i j h l => (F l).2 i j h⟩
      left_inv := fun f => rfl
      right_inv := fun F => rfl }

lemma g73u_ec_pow {γ δ : Type*} (r : γ → δ → Prop) (k : ℕ) :
    g73u_ec (fun (x : Fin k → γ) (y : Fin k → δ) => ∀ l, r (x l) (y l)) = (g73u_ec r) ^ k := by
  unfold g73u_ec
  rw [show ∀ X : Type _, Nat.card X ^ k = Nat.card (Fin k → X) from fun X => by
    rw [Nat.card_fun, Nat.card_fin]]
  refine Nat.card_congr
    { toFun := fun p l => ⟨(p.1.1 l, p.1.2 l), p.2 l⟩
      invFun := fun F => ⟨(fun l => (F l).1.1, fun l => (F l).1.2), fun l => (F l).2⟩
      left_inv := fun f => rfl
      right_inv := fun F => rfl }

lemma g73u_hc_base {m n a b : ℕ} (H : BipGraph m n) (H' : BipGraph a b) :
    g73u_hc H (fun (x y : Fin a × Fin b) => H'.adj x.1 y.2 = true) = H.bipHomCount H' * (b ^ m * a ^ n) := by
  rw [g73u_bipHomCount_eq]
  unfold g73u_hc
  have : b ^ m * a ^ n = Nat.card ((Fin m → Fin b) × (Fin n → Fin a)) := by
    simp [Nat.card_eq_fintype_card]
  rw [this, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun f => (⟨(fun i => (f.1.1 i).1, fun j => (f.1.2 j).2), f.2⟩,
        (fun i => (f.1.1 i).2, fun j => (f.1.2 j).1))
      invFun := fun F => ⟨(fun i => (F.1.1.1 i, F.2.1 i), fun j => (F.2.2 j, F.1.1.2 j)), F.1.2⟩
      left_inv := fun f => rfl
      right_inv := fun F => rfl }

lemma g73u_ec_base {a b : ℕ} (H' : BipGraph a b) :
    g73u_ec (fun (x y : Fin a × Fin b) => H'.adj x.1 y.2 = true) = H'.bipEdgeCount * (b * a) := by
  rw [g73u_bipEdgeCount_eq]
  unfold g73u_ec
  have : b * a = Nat.card (Fin b × Fin a) := by
    simp [Nat.card_eq_fintype_card]
  rw [this, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun p => (⟨(p.1.1.1, p.1.2.2), p.2⟩, (p.1.1.2, p.1.2.1))
      invFun := fun F => ⟨((F.1.1.1, F.2.1), (F.2.2, F.1.1.2)), F.1.2⟩
      left_inv := fun f => rfl
      right_inv := fun F => rfl }

noncomputable def g73u_Q {α : Type*} [Fintype α] (r : α → α → Prop) :
    BipGraph (Fintype.card α) (Fintype.card α) :=
  ⟨fun x y => @decide (r ((Fintype.equivFin α).symm x) ((Fintype.equivFin α).symm y)) (Classical.dec _)⟩

lemma g73u_Q_hc {m n : ℕ} (H : BipGraph m n) {α : Type*} [Fintype α] (r : α → α → Prop) :
    g73u_hc H (fun x y => (g73u_Q r).adj x y = true) = g73u_hc H r := by
  unfold g73u_hc
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) (Fintype.equivFin α).symm)
      (Equiv.arrowCongr (Equiv.refl _) (Fintype.equivFin α).symm)) ?_)
  intro f
  simp [g73u_Q]

lemma g73u_Q_ec {α : Type*} [Fintype α] (r : α → α → Prop) :
    g73u_ec (fun x y => (g73u_Q r).adj x y = true) = g73u_ec r := by
  unfold g73u_ec
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodCongr (Fintype.equivFin α).symm (Fintype.equivFin α).symm) ?_)
  intro f
  simp [g73u_Q]

lemma g73u_real1 (A a b hc : ℝ) (m n k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hhc : 0 ≤ hc)
    (hA : A ≤ 2 ^ m * 2 ^ n * (hc * (b ^ m * a ^ n)) ^ k) :
    A / ((a * b) ^ k + (a * b) ^ k) ^ (m + n) ≤ (hc / (a ^ m * b ^ n)) ^ k := by
  have hden : ((a * b) ^ k + (a * b) ^ k) ^ (m + n) =
      (2 ^ m * 2 ^ n) * ((a ^ m * b ^ n) * (b ^ m * a ^ n)) ^ k := by
    have e1 : (a ^ m * b ^ n) * (b ^ m * a ^ n) = (a * b) ^ (m + n) := by
      rw [mul_pow, pow_add, pow_add]; ring
    have e2 : (a * b) ^ k + (a * b) ^ k = 2 * (a * b) ^ k := by ring
    rw [e1, e2, mul_pow, pow_add (2:ℝ) m n, ← pow_mul, ← pow_mul, Nat.mul_comm k (m + n)]
  calc A / ((a * b) ^ k + (a * b) ^ k) ^ (m + n)
      ≤ 2 ^ m * 2 ^ n * (hc * (b ^ m * a ^ n)) ^ k / ((a * b) ^ k + (a * b) ^ k) ^ (m + n) :=
        div_le_div_of_nonneg_right hA (by positivity)
    _ = (hc * (b ^ m * a ^ n)) ^ k / ((a ^ m * b ^ n) * (b ^ m * a ^ n)) ^ k := by
        rw [hden, mul_div_mul_left _ _ (by positivity)]
    _ = (hc * (b ^ m * a ^ n) / ((a ^ m * b ^ n) * (b ^ m * a ^ n))) ^ k := (div_pow _ _ _).symm
    _ ≤ (hc / (a ^ m * b ^ n)) ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        rcases eq_or_ne (b ^ m * a ^ n) 0 with h | h
        · rw [h]; simp; positivity
        · rw [mul_div_mul_right _ _ h]

lemma g73u_real2 (e a b : ℝ) (k : ℕ) :
    (e * (b * a)) ^ k / ((a * b) ^ k + (a * b) ^ k) ^ 2 = (e / (a * b)) ^ k / 4 := by
  rw [show b * a = a * b by ring]
  generalize a * b = p
  rcases eq_or_ne p 0 with h | h
  · rw [h]; rcases k with _ | k
    · norm_num
    · simp
  · have hk : p ^ k ≠ 0 := pow_ne_zero _ h
    rw [div_pow, mul_pow]
    field_simp
    ring

lemma g73u_lim (d t : ℝ) (e : ℕ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (h : ∀ k : ℕ, (d ^ k / 4) ^ e ≤ t ^ k) : d ^ e ≤ t := by
  by_contra hlt
  push Not at hlt
  have hD : 0 < d ^ e := lt_of_le_of_lt ht hlt
  have hr1 : t / d ^ e < 1 := (div_lt_one hD).2 hlt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1 / 4 ^ e by positivity) hr1
  have h1 := h k
  rw [div_pow, ← pow_mul, mul_comm k e, pow_mul] at h1
  have h4 : (0:ℝ) < 4 ^ e := by positivity
  have hDk : 0 < (d ^ e) ^ k := by positivity
  rw [div_pow, div_lt_div_iff₀ hDk h4, one_mul] at hk
  rw [div_le_iff₀ h4] at h1
  linarith

theorem solution (m n : ℕ) (H : BipGraph m n) :
    AsymSidorenko H ↔ DirSidorenko (orientOf H) := by
  constructor
  · intro hA N G
    have h := hA N N ⟨G.edge⟩
    rw [g73u_L1 H]
    unfold OriGraph.dirDens OriGraph.homDens
    unfold BipGraph.bipDens BipGraph.bipHomDens at h
    have e1 : G.edgeCount = (⟨G.edge⟩ : BipGraph N N).bipEdgeCount := rfl
    have e2 : (orientOf H).homCount G = H.bipHomCount (⟨G.edge⟩ : BipGraph N N) := by
      rw [g73u_homCount_eq, g73u_bipHomCount_eq]
    rw [e1, e2, Real.rpow_two]
    simp only [Real.rpow_natCast] at h ⊢
    rw [pow_add, sq]
    exact h
  · intro hD a b H'
    have key : ∀ k : ℕ, (H'.bipDens ^ k / 4) ^ H.bipEdgeCount ≤ (H.bipHomDens H') ^ k := by
      intro k
      let rk : (Fin k → Fin a × Fin b) → (Fin k → Fin a × Fin b) → Prop :=
        fun x y => ∀ l, (fun (u v : Fin a × Fin b) => H'.adj u.1 v.2 = true) (x l) (y l)
      have hcard : Fintype.card (Fin k → Fin a × Fin b) = (a * b) ^ k := by
        simp [Fintype.card_prod]
      have h1 := hD _ (orientOf (g73u_Q rk))
      rw [g73u_L1 H, Real.rpow_natCast] at h1
      have hpow := g73u_ec_pow (fun (u v : Fin a × Fin b) => H'.adj u.1 v.2 = true) k
      have hpow2 := g73u_hc_pow H (fun (u v : Fin a × Fin b) => H'.adj u.1 v.2 = true) k
      have hdd : (orientOf (g73u_Q rk)).dirDens = H'.bipDens ^ k / 4 := by
        unfold OriGraph.dirDens
        rw [g73u_L1, g73u_bipEdgeCount_eq, g73u_Q_ec, show g73u_ec rk = _ from hpow, g73u_ec_base, Real.rpow_two,
          hcard]
        unfold BipGraph.bipDens
        push_cast
        exact g73u_real2 _ _ _ k
      have hcnt : ((orientOf H).homCount (orientOf (g73u_Q rk)) : ℝ) ≤
          2 ^ m * 2 ^ n * ((H.bipHomCount H' : ℝ) * ((b : ℝ) ^ m * (a : ℝ) ^ n)) ^ k := by
        rw [g73u_homCount_eq]
        have := g73u_hc_orient_le H (g73u_Q rk)
        rw [g73u_Q_hc, show g73u_hc H rk = _ from hpow2, g73u_hc_base] at this
        exact_mod_cast this
      have hhd : (orientOf H).homDens (orientOf (g73u_Q rk)) ≤ (H.bipHomDens H') ^ k := by
        unfold OriGraph.homDens BipGraph.bipHomDens
        rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
        generalize ((orientOf H).homCount (orientOf (g73u_Q rk)) : ℝ) = A at hcnt ⊢
        rw [hcard]
        push_cast
        exact g73u_real1 _ _ _ _ m n k (by positivity) (by positivity) (by positivity) hcnt
      rw [hdd] at h1
      exact h1.trans hhd
    have hd0 : 0 ≤ H'.bipDens := by unfold BipGraph.bipDens; positivity
    have ht0 : 0 ≤ H.bipHomDens H' := by unfold BipGraph.bipHomDens; positivity
    rw [Real.rpow_natCast]
    exact g73u_lim _ _ _ hd0 ht0 key
