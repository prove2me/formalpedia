-- Prove2me | solution 1 for FreeOrderEPTAS.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T14:14:19.573478+00:00
-- url     : https://prove2.me/submissions/d9442bf5-6827-4c95-8384-4af3b246c985

import Mathlib
import Definitions.Def_FreeOrderEPTAS_santaClaus
import Theorems.Thm_FreeOrderEPTAS_delta_calibration
import Theorems.Thm_FreeOrderEPTAS_lemma_2_2
import Theorems.Thm_FreeOrderEPTAS_constraints_I_III
import Theorems.Thm_FreeOrderEPTAS_lemma_2_3

namespace FOSol
open FreeOrderEPTAS

/-! ## Generic facts about `Prog` -/

def CostOK {α : Type} (p : Prog α) (S k : ℕ) : Prop :=
  ∀ s : Cost, s.maxSize ≤ S → ∀ r ∈ (p.run s).support, r.2.total ≤ s.total + k ∧ r.2.maxSize ≤ S

def Pres {α : Type} (p : Prog α) (P : α → Prop) : Prop :=
  ∀ s : Cost, ∀ r ∈ (p.run s).support, P r.1

def PrGE {α : Type} (p : Prog α) (G : α → Prop) (c : ENNReal) : Prop :=
  ∀ s : Cost, c ≤ (p.run s).toOuterMeasure {r | G r.1}

lemma supp_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : Cost) (r : β × Cost) :
    r ∈ ((p >>= f).run s).support ↔ ∃ x ∈ (p.run s).support, r ∈ ((f x.1).run x.2).support := by
  rw [StateT.run_bind]; exact PMF.mem_support_bind_iff _ _ _

lemma run_pure' {α : Type} (a : α) (s : Cost) : ((pure a : Prog α).run s) = PMF.pure (a, s) := rfl

lemma run_tick (k : ℕ) (s : Cost) : (tick k).run s = PMF.pure ((), { s with ops := s.ops + k }) := by
  simp [tick, StateT.run_modify]; rfl

lemma run_tick_bind {β : Type} (k : ℕ) (g : Unit → Prog β) (s : Cost) :
    (tick k >>= g).run s = (g ()).run { s with ops := s.ops + k } := by
  rw [StateT.run_bind, run_tick]; exact PMF.pure_bind _ _

lemma run_callLP (lp : LPSolver) (P : LPData) (s : Cost) :
    (callLP lp P).run s = PMF.pure (lp P, { s with
      ops := s.ops + P.size, lpCalls := s.lpCalls + 1, maxSize := max s.maxSize P.size }) := by
  simp [callLP, StateT.run_modify]; rfl

lemma run_callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) (s : Cost) :
    (callRnd rnd P y).run s = (rnd P y).bind (fun X => PMF.pure (X, { s with
      ops := s.ops + P.size, rndCalls := s.rndCalls + 1, maxSize := max s.maxSize P.size })) := by
  simp [callRnd, StateT.run_bind, StateT.run_modify]; rfl

/-! ### Cost -/

lemma costOK_pure {α : Type} (a : α) (S : ℕ) : CostOK (pure a : Prog α) S 0 := by
  intro s hs r hr
  rw [run_pure', PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact ⟨le_refl _, hs⟩

lemma costOK_mono {α : Type} {p : Prog α} {S k k' : ℕ} (h : CostOK p S k) (hk : k ≤ k') :
    CostOK p S k' := by
  intro s hs r hr
  obtain ⟨h1, h2⟩ := h s hs r hr
  exact ⟨by omega, h2⟩

lemma costOK_tick (k S : ℕ) : CostOK (tick k) S k := by
  intro s hs r hr
  rw [run_tick, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact ⟨by simp [Cost.total]; omega, hs⟩

lemma costOK_bind {α β : Type} {p : Prog α} {f : α → Prog β} {S k1 k2 : ℕ}
    (hp : CostOK p S k1) (hf : ∀ a, CostOK (f a) S k2) : CostOK (p >>= f) S (k1 + k2) := by
  intro s hs r hr
  rw [supp_bind] at hr
  obtain ⟨x, hx, hr⟩ := hr
  obtain ⟨h1, h2⟩ := hp s hs x hx
  obtain ⟨h3, h4⟩ := hf x.1 x.2 h2 r hr
  exact ⟨by omega, h4⟩

lemma costOK_callLP (lp : LPSolver) (P : LPData) {S : ℕ} (hP : P.size ≤ S) :
    CostOK (callLP lp P) S (S + 1) := by
  intro s hs r hr
  rw [run_callLP, PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; refine ⟨?_, ?_⟩
  · simp [Cost.total]; omega
  · simp; omega

lemma costOK_callRnd (rnd : Rounding) (P : LPData) (y : P.Vars) {S : ℕ} (hP : P.size ≤ S) :
    CostOK (callRnd rnd P y) S (S + 1) := by
  intro s hs r hr
  rw [run_callRnd, PMF.mem_support_bind_iff] at hr
  obtain ⟨X, -, hr⟩ := hr
  rw [PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; refine ⟨?_, ?_⟩
  · simp [Cost.total]; omega
  · simp; omega

lemma costOK_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (S c : ℕ)
    (hf : ∀ b a, CostOK (f b a) S c) : ∀ b, CostOK (foldP l f b) S (l.length * (c + 1)) := by
  induction l with
  | nil => intro b; simpa [foldP] using costOK_pure b S
  | cons a l ih =>
    intro b
    simp only [foldP]
    refine costOK_mono (costOK_bind (costOK_tick 1 S) fun _ =>
      costOK_bind (hf b a) fun b' => ih b') ?_
    simp [List.length_cons]; ring_nf; omega

lemma costOK_foldProd {α β : Type} (cs : List (List α)) :
    ∀ (f : β → List α → Prog β) (S c : ℕ), (∀ b r, CostOK (f b r) S c) →
      ∀ b, CostOK (foldProd cs f b) S ((cs.map fun l => 2 * (l.length + 1)).prod * (c + 1)) := by
  induction cs with
  | nil => intro f S c hf b; simpa [foldProd] using costOK_mono (hf b []) (by omega)
  | cons l cs ih =>
    intro f S c hf b
    simp only [foldProd]
    refine costOK_mono (costOK_foldP l _ S _ (fun b a => ih (fun b' r => f b' (a :: r)) S c
      (fun b r => hf b _) b) b) ?_
    simp only [List.map_cons, List.prod_cons]
    have hpos : 0 < (cs.map fun l => 2 * (l.length + 1)).prod := by
      apply List.prod_pos; intro x hx; simp at hx; obtain ⟨a, -, rfl⟩ := hx; omega
    have h1 : 1 ≤ (cs.map fun l => 2 * (l.length + 1)).prod * (c + 1) := by
      have := Nat.mul_le_mul hpos (Nat.succ_le_succ (Nat.zero_le c)); simpa using this
    generalize (cs.map fun l => 2 * (l.length + 1)).prod = Q at h1 ⊢
    rw [mul_assoc]
    generalize Q * (c + 1) = P at h1 ⊢
    nlinarith

/-! ### Invariants -/

lemma pres_pure {α : Type} {P : α → Prop} (a : α) (h : P a) : Pres (pure a : Prog α) P := by
  intro s r hr
  rw [run_pure', PMF.support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact h

lemma pres_bind {α β : Type} {p : Prog α} {f : α → Prog β} {Q : α → Prop} {P : β → Prop}
    (hp : Pres p Q) (hf : ∀ a, Q a → Pres (f a) P) : Pres (p >>= f) P := by
  intro s r hr
  rw [supp_bind] at hr
  obtain ⟨x, hx, hr⟩ := hr
  exact hf x.1 (hp s x hx) x.2 r hr

lemma pres_tick_bind {β : Type} {g : Unit → Prog β} {P : β → Prop} (k : ℕ)
    (h : Pres (g ()) P) : Pres (tick k >>= g) P := by
  intro s r hr
  rw [run_tick_bind] at hr
  exact h _ r hr

lemma pres_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (P : β → Prop)
    (hf : ∀ b a, P b → Pres (f b a) P) : ∀ b, P b → Pres (foldP l f b) P := by
  induction l with
  | nil => intro b hb; exact pres_pure b hb
  | cons a l ih =>
    intro b hb
    simp only [foldP]
    exact pres_tick_bind 1 (pres_bind (hf b a hb) fun b' hb' => ih b' hb')

lemma pres_foldProd {α β : Type} (cs : List (List α)) (P : β → Prop) :
    ∀ (f : β → List α → Prog β), (∀ b r, P b → Pres (f b r) P) →
      ∀ b, P b → Pres (foldProd cs f b) P := by
  induction cs with
  | nil => intro f hf b hb; exact hf b [] hb
  | cons l cs ih =>
    intro f hf b hb
    simp only [foldProd]
    exact pres_foldP l _ P (fun b a hb => ih _ (fun b' r hb' => hf b' _ hb') b hb) b hb

/-! ### Probability -/

lemma pmf_bind_ge {α β : Type} (p : PMF α) (k : α → PMF β) (S : Set β) (c : ENNReal)
    (h : ∀ x ∈ p.support, c ≤ (k x).toOuterMeasure S) : c ≤ (p.bind k).toOuterMeasure S := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc c = ∑' x, p x * c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ∑' x, p x * (k x).toOuterMeasure S := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ p.support
      · exact mul_le_mul_right (h x hx) _
      · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]

lemma pmf_bind_ge2 {α β : Type} (p : PMF α) (k : α → PMF β) (A : Set α) (S : Set β)
    (h : ∀ x ∈ p.support, x ∈ A → (k x).support ⊆ S) :
    p.toOuterMeasure A ≤ (p.bind k).toOuterMeasure S := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA]
    by_cases hx : x ∈ p.support
    · rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (h x hx hxA), mul_one]
    · rw [PMF.mem_support_iff, not_not] at hx; simp [hx]
  · rw [Set.indicator_of_notMem hxA]; exact zero_le

lemma prGE_tick_bind {β : Type} {g : Unit → Prog β} {G : β → Prop} {c : ENNReal} (k : ℕ)
    (h : PrGE (g ()) G c) : PrGE (tick k >>= g) G c := by
  intro s; rw [run_tick_bind]; exact h _

lemma prGE_foldP {α β : Type} (l : List α) (f : β → α → Prog β) (Inv G : β → Prop) (c : ENNReal)
    (hInv : ∀ b a, Inv b → Pres (f b a) Inv)
    (hG : ∀ b a, Inv b ∧ G b → Pres (f b a) (fun b => Inv b ∧ G b))
    (a0 : α) (ha0 : a0 ∈ l) (h0 : ∀ b, Inv b → PrGE (f b a0) G c) :
    ∀ b, Inv b → PrGE (foldP l f b) G c := by
  induction l with
  | nil => simp at ha0
  | cons a l ih =>
    intro b hb
    simp only [foldP]
    refine prGE_tick_bind 1 fun s => ?_
    rw [StateT.run_bind]
    rcases List.mem_cons.1 ha0 with rfl | hmem
    · refine le_trans (h0 b hb s) (pmf_bind_ge2 _ _ _ _ fun x hx hxG => ?_)
      have hI : Inv x.1 := hInv b a0 hb s x hx
      intro r hr
      exact (pres_foldP l f _ hG x.1 ⟨hI, hxG⟩ x.2 r hr).2
    · exact pmf_bind_ge _ _ _ _ fun x hx => ih hmem x.1 (hInv b a hb s x hx) x.2

lemma prGE_foldProd {α β : Type} (cs : List (List α)) (Inv G : β → Prop) (c : ENNReal) :
    ∀ (f : β → List α → Prog β) (g0 : List α), List.Forall₂ (fun a l => a ∈ l) g0 cs →
    (∀ b r, Inv b → Pres (f b r) Inv) →
    (∀ b r, Inv b ∧ G b → Pres (f b r) (fun b => Inv b ∧ G b)) →
    (∀ b, Inv b → PrGE (f b g0) G c) →
    ∀ b, Inv b → PrGE (foldProd cs f b) G c := by
  induction cs with
  | nil => intro f g0 hg hInv hG h0 b hb; cases hg; exact h0 b hb
  | cons l cs ih =>
    intro f g0 hg hInv hG h0 b hb
    cases hg with
    | cons ha hg' =>
      rename_i a0 g1
      simp only [foldProd]
      refine prGE_foldP l _ Inv G c
        (fun b a hb => pres_foldProd cs Inv _ (fun b' r hb' => hInv b' _ hb') b hb)
        (fun b a hb => pres_foldProd cs _ _ (fun b' r hb' => hG b' _ hb') b hb)
        a0 ha (fun b hb => ih _ g1 hg' (fun b' r hb' => hInv b' _ hb')
          (fun b' r hb' => hG b' _ hb') (fun b' hb' => h0 b' hb') b hb) b hb

/-! ## The verification `check` -/

lemma countP_sum {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = (l.map fun i => if p i = true then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.countP_cons, ih]; simp; omega

lemma filter_len_eq {k : ℕ} (p : Fin k → Bool) :
    ((List.finRange k).filter p).length = (Finset.univ.filter fun i => p i = true).card := by
  rw [Finset.card_filter, Fin.sum_univ_def, ← List.countP_eq_length_filter, countP_sum]

lemma check_iff {m D n : ℕ} (I : SCInstance m D n) (c : ℝ) (X : Assignment m n) :
    check I c X = true ↔ MeetsCard I X ∧ LoadAtLeast I X c := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, filter_len_eq,
    MeetsCard, LoadAtLeast, load, Fin.sum_univ_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun i => (h2 i).1⟩, fun i d hd => ?_⟩
    rcases (h2 i).2 d with h | h
    · exact absurd hd h
    · exact h
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun i => ⟨h2 i, fun d => ?_⟩⟩
    by_cases hd : d ∈ I.A i
    · exact Or.inr (h3 i d hd)
    · exact Or.inl hd

/-! ## List lemmas -/

lemma length_flatMap_uniform {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hk : ∀ a, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, hk, ih]; ring

lemma getD_flatMap_uniform {α β : Type} (f : α → List β) (k : ℕ)
    (hk : ∀ a, (f a).length = k) (j : ℕ) (hj : j < k) (d : β) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length),
      (l.flatMap f).getD (i * k + j) d = (f l[i]).getD j d := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi
    rw [List.flatMap_cons]
    rcases i with _ | i
    · simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by rw [hk]; exact hj)]
    · rw [List.getD_append_right _ _ _ _ (by rw [hk]; nlinarith)]
      have : (i + 1) * k + j - (f a).length = i * k + j := by rw [hk]; ring_nf; omega
      rw [this, ih i (by simpa using hi)]
      simp

lemma forall₂_flatMap {α β γ : Type} (R : β → γ → Prop) (f : α → List β) (g : α → List γ)
    (h : ∀ a, List.Forall₂ R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons]; exact List.rel_append (h a) ih

lemma forall₂_map {α β γ : Type} (R : β → γ → Prop) (f : α → β) (g : α → γ)
    (h : ∀ a, R (f a) (g a)) : ∀ l : List α, List.Forall₂ R (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons]; exact List.Forall₂.cons (h a) ih

lemma forall₂_replicate {α : Type} (c : List α) :
    ∀ g : List α, (∀ x ∈ g, x ∈ c) → List.Forall₂ (fun a l => a ∈ l) g (List.replicate g.length c) := by
  intro g
  induction g with
  | nil => intro _; simp
  | cons a g ih =>
    intro h
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-! ## The program -/

def Ver {m D n : ℕ} (I : SCInstance m D n) (ε : ℝ) (X : Assignment m n) : Prop :=
  MeetsCard I X ∧ LoadAtLeast I X (1 - ε)

def Inv {m D n : ℕ} (I : SCInstance m D n) (ε : ℝ) (b : Option (Assignment m n)) : Prop :=
  ∀ X, b = some X → Ver I ε X

def Good {m D n : ℕ} (I : SCInstance m D n) (ε : ℝ) (b : Option (Assignment m n)) : Prop :=
  ∃ X, b = some X ∧ Ver I ε X

lemma santa_pres {m D n : ℕ} (ε : ℝ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding) :
    Pres (santaClaus ε I lp rnd) (Inv I ε) := by
  simp only [santaClaus, opn, bind_assoc, pure_bind]
  refine pres_tick_bind _ <| pres_tick_bind _ <| pres_tick_bind _ <| pres_tick_bind _ <|
    pres_tick_bind _ <| pres_tick_bind _ <| pres_tick_bind _ <| pres_tick_bind _ <|
    pres_foldProd _ _ _ ?_ _ (by simp [Inv])
  intro b gN hb
  refine pres_foldProd _ _ _ ?_ _ hb
  intro b gS hb
  cases b with
  | some X => exact pres_pure _ hb
  | none =>
    dsimp only
    refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun o _ => ?_
    cases o with
    | none => exact pres_pure _ (by simp [Inv])
    | some y =>
      dsimp only
      refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun X _ =>
        pres_tick_bind _ (pres_pure _ ?_)
      intro X' hX'
      split_ifs at hX' with h
      cases hX'
      exact (check_iff I _ X).1 h

lemma numTypes_le {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) : numTypes I ϵ δ ≤ n := by
  unfold numTypes typeList
  exact (List.dedup_sublist _).length_le.trans (by simp)

lemma size_le {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ) (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ) :
    (mkLP I ϵ δ ξ Nlo Nhi Slo).size ≤ 6 * (m + 1) * (D + 2) * (n + 1) := by
  have hT := numTypes_le I ϵ δ
  simp only [LPData.size, mkLP]
  have h1 : m * numTypes I ϵ δ ≤ m * n := Nat.mul_le_mul_left _ hT
  have h2 : m * D * numTypes I ϵ δ ≤ m * D * n := Nat.mul_le_mul_left _ hT
  nlinarith [Nat.zero_le (m * D * n), Nat.zero_le (m * n), Nat.zero_le (D * n), Nat.zero_le (m * D)]

noncomputable def Kx {m D n : ℕ} (ε : ℝ) (I : SCInstance m D n) : ℕ :=
  1 + (1 + (8 + ((calib (ε / 2) m D + 1) + (11 * (n + 1) * (m + 1) * (D + 1) +
    (4 * (n + 1) * (n + 1) * (m + 1) * (D + 1) +
    ((calib (ε / 2) m D + 6 + 3 * (nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length) +
    ((3 * ((m + 1) * (D + 1) * (numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D) + 1) *
        ((sGrid (ε / 2) (numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))).length + 1)) + 6) +
    ((List.replicate (m * numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))
        (nGrid (ε / 2 / 2) (calib (ε / 2) m D) n)).map fun l => 2 * (l.length + 1)).prod *
      ((((sChoices I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D)).map
          fun l => 2 * (l.length + 1)).prod *
        (((6 * (m + 1) * (D + 2) * (n + 1) + 1) + ((6 * (m + 1) * (D + 2) * (n + 1) + 1) +
          (4 * (m + 1) * (n + 1) * (D + 1) + 0))) + 1)) + 1))))))))

lemma santa_cost {m D n : ℕ} (ε : ℝ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding) :
    CostOK (santaClaus ε I lp rnd) (6 * (m + 1) * (D + 2) * (n + 1)) (Kx ε I) := by
  simp only [santaClaus, opn, bind_assoc, pure_bind, Kx]
  refine costOK_bind (costOK_tick _ _) fun _ => costOK_bind (costOK_tick _ _) fun _ =>
    costOK_bind (costOK_tick _ _) fun _ => costOK_bind (costOK_tick _ _) fun _ =>
    costOK_bind (costOK_tick _ _) fun _ => costOK_bind (costOK_tick _ _) fun _ =>
    costOK_bind (costOK_tick _ _) fun _ => costOK_bind (costOK_tick _ _) fun _ =>
    costOK_foldProd _ _ _ _ (fun b gN => costOK_foldProd _ _ _ _ (fun b gS => ?_) b) none
  cases b with
  | some X => exact costOK_mono (costOK_pure _ _) (Nat.zero_le _)
  | none =>
    dsimp only
    refine costOK_bind (costOK_callLP lp _ (size_le _ _ _ _ _ _ _)) fun o => ?_
    cases o with
    | none => exact costOK_mono (costOK_pure _ _) (Nat.zero_le _)
    | some y =>
      dsimp only
      exact costOK_bind (costOK_callRnd rnd _ y (size_le _ _ _ _ _ _ _)) fun X =>
        costOK_bind (costOK_tick _ _) fun _ => costOK_pure _ _

/-! ## Numeric bounds -/

def Rb (q m D : ℕ) : ℕ := (8 * (m * D + 1) * (2 * q + 1)) ^ 2
def Tb (q m D : ℕ) : ℕ := (4 * q * Rb q m D + 1) ^ (m * D)
def Ab (q m D : ℕ) : ℕ := 2 * 2 ^ Rb q m D + 4 + 4 * q
def Mb (q m D : ℕ) : ℕ := m * Tb q m D
def Gb (q m D : ℕ) : ℕ := 3 * (Mb q m D).factorial * Ab q m D ^ Mb q m D
def Sb (q m D : ℕ) : ℕ := 2 * q * Tb q m D + 2

lemma inv_le_q {ε : ℝ} {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) : 1 / ε ≤ q := by
  rw [← hq]; exact Nat.le_ceil _

lemma calib_le {ε : ℝ} (hε0 : 0 < ε) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (m D : ℕ) :
    calib (ε / 2) m D ≤ Rb q m D := by
  have h1 : ⌈1 / (ε / 2)⌉₊ ≤ 2 * q := by
    rw [Nat.ceil_le]
    have := inv_le_q hq
    have e : 1 / (ε / 2) = 2 * (1 / ε) := by field_simp
    rw [e]; push_cast; linarith
  unfold calib Rb
  gcongr

lemma seg_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (r R : ℕ)
    (hr : r ≤ R) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    seg (ε / 2) ((1 / 2 : ℝ) ^ r) v ≤ 4 * q * R := by
  unfold seg
  split_ifs with h
  · exact Nat.zero_le _
  push_neg at h
  have hδ : (0 : ℝ) < (1 / 2) ^ r := by positivity
  have hv1 : v ≤ 1 := hv.2
  rw [Nat.ceil_le]
  have hl1 : 0 ≤ Real.log (v / (1 / 2) ^ r) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ]; linarith
  have hl2 : Real.log (v / (1 / 2) ^ r) ≤ r := by
    calc Real.log (v / (1 / 2) ^ r) ≤ Real.log (2 ^ r) := by
          apply Real.log_le_log (div_pos (by linarith) hδ)
          rw [div_le_iff₀ hδ, ← mul_pow]; norm_num; exact hv1
      _ = r * Real.log 2 := by rw [Real.log_pow]
      _ ≤ r * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have := Real.log_two_lt_d9; linarith
      _ = r := by ring
  have hl3 : ε / 2 / 2 ≤ Real.log (1 + ε / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 1 + ε / 2) (by linarith)
    have e : 1 - (1 + ε / 2)⁻¹ = (ε / 2) / (1 + ε / 2) := by field_simp; ring
    rw [e] at this
    refine le_trans ?_ this
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have hq' := inv_le_q hq
  calc Real.log (v / (1 / 2) ^ r) / Real.log (1 + ε / 2) ≤ r / (ε / 2 / 2) :=
        div_le_div₀ (Nat.cast_nonneg _) hl2 (by positivity) hl3
    _ = 4 * r * (1 / ε) := by field_simp; ring
    _ ≤ 4 * R * q := by
        have : (r : ℝ) ≤ R := by exact_mod_cast hr
        gcongr
    _ = ((4 * q * R : ℕ) : ℝ) := by push_cast; ring

lemma numTypes_le_Tb {m D n : ℕ} (I : SCInstance m D n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) :
    numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D) ≤ Tb q m D := by
  set K := 4 * q * Rb q m D
  let F : Finset (Fin m → Fin D → ℕ) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.range (K + 1)
  have hsub : (typeList I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D)).toFinset ⊆ F := by
    intro x hx
    simp only [typeList, List.mem_toFinset, List.mem_dedup, List.mem_map, List.mem_finRange,
      true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    simp only [F, Fintype.mem_piFinset, Finset.mem_range]
    intro i d
    unfold typeVec
    split_ifs
    · exact Nat.lt_succ_of_le (seg_le hε0 hε1 hq _ _ (calib_le hε0 hq m D) _ (I.ℓ_mem i j d))
    · omega
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (by unfold typeList; exact List.nodup_dedup _)] at hc
  unfold numTypes
  refine hc.trans (le_of_eq ?_)
  simp only [F, Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Tb]
  rw [← pow_mul, mul_comm]

lemma log_le_log_succ (n : ℕ) : Real.log n ≤ Real.log (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_le_log (by exact_mod_cast hn) (by linarith)

lemma NG_real {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (m D n : ℕ) :
    (((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1 : ℕ) : ℝ) ≤
      Ab q m D * (1 + Real.log (n + 1)) := by
  set ξ := ε / 2 / 2 with hξ
  have hξ0 : 0 < ξ := by positivity
  have hξ1 : ξ < 1 := by rw [hξ]; linarith
  have hr := calib_le hε0 hq m D
  simp only [nGrid, List.length_append, List.length_map, List.length_range]
  set L := ⌈Real.log n / Real.log (1 / (1 - ξ))⌉₊
  have hlogξ : ξ ≤ Real.log (1 / (1 - ξ)) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos (x := 1 - ξ) (by linarith)
    linarith
  have hy0 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hL : (L : ℝ) ≤ 4 * q * Real.log (n + 1) + 1 := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg hlogn (le_trans hξ0.le hlogξ))
    have h2 : Real.log n / Real.log (1 / (1 - ξ)) ≤ Real.log n / ξ :=
      div_le_div_of_nonneg_left hlogn hξ0 hlogξ
    have h3 : Real.log n / ξ = 4 * Real.log n * (1 / ε) := by rw [hξ]; field_simp; ring
    have h4 := inv_le_q hq
    have h5 := log_le_log_succ n
    have h6 : 4 * Real.log n * (1 / ε) ≤ 4 * Real.log (n + 1) * q := by gcongr
    linarith
  have hpow : ((2 : ℕ) ^ calib (ε / 2) m D : ℝ) ≤ (2 : ℝ) ^ Rb q m D := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hr
  have hA : (Ab q m D : ℝ) = 2 * 2 ^ Rb q m D + 4 + 4 * q := by simp [Ab]
  push_cast at hpow ⊢
  rw [hA]
  have : (0 : ℝ) ≤ 2 ^ Rb q m D := by positivity
  nlinarith

lemma NG_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (m D n : ℕ) :
    (nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1 ≤ Ab q m D * (n + 1) := by
  have h := NG_real hε0 hε1 hq m D n
  have h2 : 1 + Real.log (n + 1) ≤ n + 1 := by
    have := Real.log_le_sub_one_of_pos (x := (n : ℝ) + 1) (by positivity); linarith
  have h3 : (Ab q m D : ℝ) * (1 + Real.log (n + 1)) ≤ Ab q m D * (n + 1) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  exact_mod_cast h.trans h3

lemma NG_pow_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (m D n : ℕ) :
    ((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1) ^ Mb q m D ≤ Gb q m D * (n + 1) := by
  have h := NG_real hε0 hε1 hq m D n
  set M := Mb q m D
  set y := Real.log (n + 1)
  have hy0 : 0 ≤ y := Real.log_nonneg (by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith)
  have h1 : ((((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1 : ℕ) : ℝ)) ^ M ≤
      (Ab q m D : ℝ) ^ M * (1 + y) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) h M
  have h2 := Real.pow_div_factorial_le_exp (1 + y) (by linarith) M
  have h3 : Real.exp (1 + y) ≤ 3 * (n + 1) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ n + 1 := by positivity
    nlinarith
  have hf : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have h4 : (1 + y) ^ M ≤ M.factorial * (3 * (n + 1)) := by
    rw [div_le_iff₀ hf] at h2; nlinarith
  have h5 : (((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1 : ℕ) : ℝ) ^ M ≤
      ((Gb q m D * (n + 1) : ℕ) : ℝ) := by
    refine h1.trans ?_
    have : (0 : ℝ) ≤ (Ab q m D : ℝ) ^ M := by positivity
    calc (Ab q m D : ℝ) ^ M * (1 + y) ^ M ≤ (Ab q m D : ℝ) ^ M * (M.factorial * (3 * (n + 1))) :=
          mul_le_mul_of_nonneg_left h4 this
      _ = ((Gb q m D * (n + 1) : ℕ) : ℝ) := by simp [Gb, M]; ring
  exact_mod_cast h5

lemma sGrid_le {ε : ℝ} (hε0 : 0 < ε) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) (m D T : ℕ) (hT : T ≤ Tb q m D) :
    (sGrid (ε / 2) T).length + 1 ≤ Sb q m D := by
  have hlen : (sGrid (ε / 2) T).length = ⌊(T : ℝ) / (ε / 2)⌋₊ + 1 := by
    simp [sGrid]
  rw [hlen, Sb]
  have : ⌊(T : ℝ) / (ε / 2)⌋₊ ≤ 2 * q * Tb q m D := by
    refine (Nat.floor_le_floor ?_).trans (Nat.floor_natCast _).le
    have h1 := inv_le_q hq
    have h2 : (T : ℝ) ≤ Tb q m D := by exact_mod_cast hT
    have e : (T : ℝ) / (ε / 2) = 2 * T * (1 / ε) := by field_simp
    rw [e]; push_cast
    calc 2 * (T : ℝ) * (1 / ε) ≤ 2 * (Tb q m D) * q := by gcongr
      _ = 2 * q * Tb q m D := by ring
  omega

lemma prodNG_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) {m D n : ℕ}
    (I : SCInstance m D n) :
    ((List.replicate (m * numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))
        (nGrid (ε / 2 / 2) (calib (ε / 2) m D) n)).map fun l => 2 * (l.length + 1)).prod ≤
      2 ^ Mb q m D * Gb q m D * (n + 1) := by
  rw [List.map_replicate, List.prod_replicate]
  have hT := numTypes_le_Tb I hε0 hε1 hq
  have hk : m * numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D) ≤ Mb q m D :=
    Nat.mul_le_mul_left _ hT
  calc (2 * ((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1)) ^
        (m * numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))
      ≤ (2 * ((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1)) ^ Mb q m D :=
        Nat.pow_le_pow_right (by omega) hk
    _ = 2 ^ Mb q m D * ((nGrid (ε / 2 / 2) (calib (ε / 2) m D) n).length + 1) ^ Mb q m D := by
        rw [mul_pow]
    _ ≤ 2 ^ Mb q m D * (Gb q m D * (n + 1)) :=
        Nat.mul_le_mul_left _ (NG_pow_le hε0 hε1 hq m D n)
    _ = _ := by ring

lemma prodSC_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) {m D n : ℕ}
    (I : SCInstance m D n) :
    ((sChoices I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D)).map
        fun l => 2 * (l.length + 1)).prod ≤ (2 * Sb q m D) ^ (m * D * Tb q m D) := by
  have hT := numTypes_le_Tb I hε0 hε1 hq
  have hS2 : 2 ≤ Sb q m D := by unfold Sb; omega
  have hmem : ∀ x ∈ (sChoices I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D)).map
      (fun l => 2 * (l.length + 1)), x ≤ 2 * Sb q m D := by
    intro x hx
    simp only [List.mem_map, sChoices, List.mem_flatMap, List.mem_finRange, true_and] at hx
    obtain ⟨l, ⟨i, d, t, rfl⟩, rfl⟩ := hx
    split_ifs
    · have := sGrid_le hε0 hq m D _ hT; omega
    · simp; omega
  refine (List.prod_le_pow_card _ _ hmem).trans (Nat.pow_le_pow_right (by omega) ?_)
  rw [List.length_map, sChoices,
    length_flatMap_uniform _ _ (D * numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))]
  · simp only [List.length_finRange]
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT)
  · intro i
    rw [length_flatMap_uniform _ _ (numTypes I (ε / 2) ((1 / 2 : ℝ) ^ calib (ε / 2) m D))]
    · simp
    · intro d; simp

lemma le_sq_of {a c N : ℕ} (h : a ≤ c * N) (hN : 1 ≤ N) : a ≤ c * N ^ 2 := by
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  nlinarith

lemma const_le_sq {a c N : ℕ} (h : a ≤ c) (hN : 1 ≤ N) : a ≤ c * N ^ 2 := by
  refine le_sq_of (h.trans ?_) hN
  nlinarith

def Bc (m D : ℕ) : ℕ := 12 * (m + 1) * (D + 2) + 4 * (m + 1) * (D + 1) + 3

def Cb (q m D : ℕ) : ℕ :=
  1 + (1 + (8 + ((Rb q m D + 1) + (11 * (m + 1) * (D + 1) + (4 * (m + 1) * (D + 1) +
    ((Rb q m D + 6 + 3 * Ab q m D) + ((3 * ((m + 1) * (D + 1) * (Tb q m D + 1) * Sb q m D) + 6) +
    2 ^ Mb q m D * Gb q m D * ((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1))))))))

lemma Kx_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {q : ℕ} (hq : ⌈1 / ε⌉₊ = q) {m D n : ℕ}
    (I : SCInstance m D n) : Kx ε I ≤ Cb q m D * (n + 1) ^ 2 := by
  have hN : 1 ≤ n + 1 := by omega
  have hr := calib_le hε0 hq m D
  have hT := numTypes_le_Tb I hε0 hε1 hq
  have hNG := NG_le hε0 hε1 hq m D n
  have hsg := sGrid_le hε0 hq m D _ hT
  have hPN := prodNG_le hε0 hε1 hq I
  have hPS := prodSC_le hε0 hε1 hq I
  set r := calib (ε / 2) m D
  set T := numTypes I (ε / 2) ((1 / 2 : ℝ) ^ r)
  set NGl := (nGrid (ε / 2 / 2) r n).length
  have e1 : 1 ≤ 1 * (n + 1) ^ 2 := const_le_sq (le_refl 1) hN
  have e2 : 8 ≤ 8 * (n + 1) ^ 2 := const_le_sq (le_refl 8) hN
  have e3 : r + 1 ≤ (Rb q m D + 1) * (n + 1) ^ 2 := const_le_sq (by omega) hN
  have e4 : 11 * (n + 1) * (m + 1) * (D + 1) ≤ (11 * (m + 1) * (D + 1)) * (n + 1) ^ 2 :=
    le_sq_of (le_of_eq (by ring)) hN
  have e5 : 4 * (n + 1) * (n + 1) * (m + 1) * (D + 1) = (4 * (m + 1) * (D + 1)) * (n + 1) ^ 2 := by
    ring
  have e6 : r + 6 + 3 * NGl ≤ (Rb q m D + 6 + 3 * Ab q m D) * (n + 1) ^ 2 := by
    refine le_sq_of ?_ hN
    have h1 : (Rb q m D + 6 + 3 * Ab q m D) * (n + 1) =
        (Rb q m D + 6) * (n + 1) + 3 * (Ab q m D * (n + 1)) := by ring
    have h2 : Rb q m D + 6 ≤ (Rb q m D + 6) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [h1]; omega
  have e7 : 3 * ((m + 1) * (D + 1) * (T + 1) * ((sGrid (ε / 2) T).length + 1)) + 6 ≤
      (3 * ((m + 1) * (D + 1) * (Tb q m D + 1) * Sb q m D) + 6) * (n + 1) ^ 2 := by
    refine const_le_sq ?_ hN
    have h1 : (m + 1) * (D + 1) * (T + 1) ≤ (m + 1) * (D + 1) * (Tb q m D + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 := Nat.mul_le_mul h1 hsg
    omega
  have e8 : ((List.replicate (m * T) (nGrid (ε / 2 / 2) r n)).map
        fun l => 2 * (l.length + 1)).prod *
      ((((sChoices I (ε / 2) ((1 / 2 : ℝ) ^ r)).map fun l => 2 * (l.length + 1)).prod *
        (((6 * (m + 1) * (D + 2) * (n + 1) + 1) + ((6 * (m + 1) * (D + 2) * (n + 1) + 1) +
          (4 * (m + 1) * (n + 1) * (D + 1) + 0))) + 1)) + 1) ≤
      (2 ^ Mb q m D * Gb q m D * ((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1)) *
        (n + 1) ^ 2 := by
    revert hPN hPS
    generalize ((List.replicate (m * T) (nGrid (ε / 2 / 2) r n)).map
        fun l => 2 * (l.length + 1)).prod = PN
    generalize ((sChoices I (ε / 2) ((1 / 2 : ℝ) ^ r)).map fun l => 2 * (l.length + 1)).prod = PS
    intro hPS hPN
    have hB : (6 * (m + 1) * (D + 2) * (n + 1) + 1 + (6 * (m + 1) * (D + 2) * (n + 1) + 1 +
        (4 * (m + 1) * (n + 1) * (D + 1) + 0)) + 1) ≤ Bc m D * (n + 1) := by
      have : Bc m D * (n + 1) = (12 * (m + 1) * (D + 2) + 4 * (m + 1) * (D + 1)) * (n + 1) +
          3 * (n + 1) := by unfold Bc; ring
      rw [this]
      have : (12 * (m + 1) * (D + 2) + 4 * (m + 1) * (D + 1)) * (n + 1) =
          6 * (m + 1) * (D + 2) * (n + 1) + 6 * (m + 1) * (D + 2) * (n + 1) +
            4 * (m + 1) * (n + 1) * (D + 1) := by ring
      omega
    have h1 : PS * (6 * (m + 1) * (D + 2) * (n + 1) + 1 + (6 * (m + 1) * (D + 2) * (n + 1) + 1 +
        (4 * (m + 1) * (n + 1) * (D + 1) + 0)) + 1) + 1 ≤
        ((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1) * (n + 1) := by
      revert hB
      generalize (6 * (m + 1) * (D + 2) * (n + 1) + 1 + (6 * (m + 1) * (D + 2) * (n + 1) + 1 +
        (4 * (m + 1) * (n + 1) * (D + 1) + 0)) + 1) = Bv
      intro hB
      have := Nat.mul_le_mul hPS hB
      generalize PS * Bv = X at this ⊢
      have e : ((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1) * (n + 1) =
          (2 * Sb q m D) ^ (m * D * Tb q m D) * (Bc m D * (n + 1)) + (n + 1) := by ring
      rw [e]; exact Nat.add_le_add this hN
    calc PN * (PS * (6 * (m + 1) * (D + 2) * (n + 1) + 1 + (6 * (m + 1) * (D + 2) * (n + 1) + 1 +
        (4 * (m + 1) * (n + 1) * (D + 1) + 0)) + 1) + 1)
        ≤ (2 ^ Mb q m D * Gb q m D * (n + 1)) *
          (((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1) * (n + 1)) := Nat.mul_le_mul hPN h1
      _ = _ := by ring
  unfold Kx Cb
  calc _ ≤ 1 * (n + 1) ^ 2 + (1 * (n + 1) ^ 2 + (8 * (n + 1) ^ 2 +
      ((Rb q m D + 1) * (n + 1) ^ 2 + ((11 * (m + 1) * (D + 1)) * (n + 1) ^ 2 +
      ((4 * (m + 1) * (D + 1)) * (n + 1) ^ 2 + ((Rb q m D + 6 + 3 * Ab q m D) * (n + 1) ^ 2 +
      ((3 * ((m + 1) * (D + 1) * (Tb q m D + 1) * Sb q m D) + 6) * (n + 1) ^ 2 +
      (2 ^ Mb q m D * Gb q m D * ((2 * Sb q m D) ^ (m * D * Tb q m D) * Bc m D + 1)) *
        (n + 1) ^ 2))))))) := by
        exact add_le_add e1 (add_le_add e1 (add_le_add e2 (add_le_add e3 (add_le_add e4
          (add_le_add e5.le (add_le_add e6 (add_le_add e7 e8)))))))
    _ = _ := by ring

/-! ## The induced guess -/

section Guess
variable {m D n : ℕ} (I : SCInstance m D n) (ϵ ξ : ℝ) (r : ℕ) (x : Assignment m n)

noncomputable def kOf (N : ℕ) : ℕ := ⌊Real.log N / Real.log (1 / (1 - ξ))⌋₊

noncomputable def wN (i : Fin m) (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) : ℕ × ℕ :=
  if (Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t : ℝ) ≤ 2 / (1 / 2 : ℝ) ^ r then
    (Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t, Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t)
  else (2 ^ r, ⌈((1 - ξ) ^ kOf ξ (Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t))⁻¹⌉₊)

noncomputable def gN : List (ℕ × ℕ) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange (numTypes I ϵ ((1 / 2 : ℝ) ^ r))).map fun t => wN I ϵ ξ r x i t

noncomputable def vS (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) : ℝ :=
  if d ∈ I.A i ∧ typeOf I ϵ ((1 / 2 : ℝ) ^ r) t i d = 0 then
    (⌊min (Sip I ϵ ((1 / 2 : ℝ) ^ r) x i d t) 1 /
      (ϵ / (numTypes I ϵ ((1 / 2 : ℝ) ^ r) : ℝ))⌋₊ : ℝ) * (ϵ / (numTypes I ϵ ((1 / 2 : ℝ) ^ r) : ℝ))
  else 0

noncomputable def gS : List ℝ :=
  (List.finRange m).flatMap fun i => (List.finRange D).flatMap fun d =>
    (List.finRange (numTypes I ϵ ((1 / 2 : ℝ) ^ r))).map fun t => vS I ϵ r x i d t

lemma nAt_gN (i : Fin m) (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) :
    nAt (gN I ϵ ξ r x) i t = wN I ϵ ξ r x i t := by
  unfold nAt gN
  rw [getD_flatMap_uniform _ (numTypes I ϵ ((1 / 2 : ℝ) ^ r))
    (fun _ => by rw [List.length_map, List.length_finRange]) t.val t.isLt _ _ i.val (by simp)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_finRange]; exact t.isLt)]
  simp

lemma sAt_gS (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) :
    sAt (gS I ϵ r x) i d t = vS I ϵ r x i d t := by
  unfold sAt gS
  have e : (i.val * D + d.val) * numTypes I ϵ ((1 / 2 : ℝ) ^ r) + t.val =
      i.val * (D * numTypes I ϵ ((1 / 2 : ℝ) ^ r)) +
        (d.val * numTypes I ϵ ((1 / 2 : ℝ) ^ r) + t.val) := by ring
  have ht := t.isLt
  have hd := d.isLt
  rw [e, getD_flatMap_uniform _ (D * numTypes I ϵ ((1 / 2 : ℝ) ^ r))
    (fun _ => by
      rw [length_flatMap_uniform _ _ (numTypes I ϵ ((1 / 2 : ℝ) ^ r))
        (fun _ => by rw [List.length_map, List.length_finRange]), List.length_finRange])
    _ (by nlinarith) _ _ i.val (by simp)]
  rw [getD_flatMap_uniform _ (numTypes I ϵ ((1 / 2 : ℝ) ^ r))
    (fun _ => by rw [List.length_map, List.length_finRange]) _ ht _ _ d.val (by simp)]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_finRange]; exact t.isLt)]
  simp

lemma two_div_half_pow (r : ℕ) : (2 : ℝ) / (1 / 2) ^ r = 2 * 2 ^ r := by
  rw [one_div_pow, div_div_eq_mul_div, div_one]

lemma one_div_half_pow (r : ℕ) : (1 : ℝ) / (1 / 2) ^ r = 2 ^ r := by
  rw [one_div_pow, one_div_one_div]

lemma Nip_le (i : Fin m) (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) :
    Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t ≤ n := by
  unfold Nip
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma kOf_spec {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 - ξ) * N ≤ (⌈((1 - ξ) ^ kOf ξ N)⁻¹⌉₊ : ℝ) ∧ ⌈((1 - ξ) ^ kOf ξ N)⁻¹⌉₊ ≤ N := by
  set a : ℝ := 1 / (1 - ξ) with ha
  have ha1 : 1 < a := by rw [ha, lt_div_iff₀ (by linarith)]; linarith
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : ((1 - ξ) ^ kOf ξ N)⁻¹ = a ^ kOf ξ N := by rw [ha, one_div, inv_pow]
  rw [hinv]
  have hk : (kOf ξ N : ℝ) ≤ Real.log N / Real.log a :=
    Nat.floor_le (div_nonneg (Real.log_natCast_nonneg N) hla.le)
  have hk2 : Real.log N / Real.log a < kOf ξ N + 1 := Nat.lt_floor_add_one _
  have h1 : a ^ kOf ξ N ≤ N := by
    rw [← Real.log_le_log_iff (by positivity) hNpos, Real.log_pow]
    rwa [le_div_iff₀ hla] at hk
  have h2 : (N : ℝ) < a ^ (kOf ξ N + 1) := by
    rw [← Real.log_lt_log_iff hNpos (by positivity), Real.log_pow]
    rw [div_lt_iff₀ hla] at hk2; push_cast; linarith
  refine ⟨?_, Nat.ceil_le.2 h1⟩
  refine le_trans ?_ (Nat.le_ceil _)
  have e : (1 - ξ) * a ^ (kOf ξ N + 1) = a ^ kOf ξ N := by
    have hb : (1 - ξ) * a = 1 := by rw [ha, mul_one_div_cancel (by linarith)]
    rw [pow_succ, mul_comm (a ^ kOf ξ N) a, ← mul_assoc, hb, one_mul]
  rw [← e]
  exact mul_le_mul_of_nonneg_left h2.le (by linarith)

lemma wN_mem {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (i : Fin m)
    (t : Fin (numTypes I ϵ ((1 / 2 : ℝ) ^ r))) : wN I ϵ ξ r x i t ∈ nGrid ξ r n := by
  unfold wN nGrid
  have hNn := Nip_le I ϵ r x i t
  split_ifs with h
  · rw [two_div_half_pow] at h
    have : Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t ≤ 2 * 2 ^ r := by exact_mod_cast h
    exact List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩)
  · refine List.mem_append_right _ (List.mem_map.2 ⟨kOf ξ (Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t),
      List.mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩)
    push_neg at h
    have hpos : (0 : ℝ) < Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t := lt_trans (by positivity) h
    have hla : 0 ≤ Real.log (1 / (1 - ξ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    unfold kOf
    refine (Nat.floor_le_floor ?_).trans (Nat.floor_le_ceil _)
    apply div_le_div_of_nonneg_right _ hla
    exact Real.log_le_log hpos (by exact_mod_cast hNn)

lemma gN_forall {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    List.Forall₂ (fun a l => a ∈ l) (gN I ϵ ξ r x)
      (List.replicate (m * numTypes I ϵ ((1 / 2 : ℝ) ^ r)) (nGrid ξ r n)) := by
  have hlen : (gN I ϵ ξ r x).length = m * numTypes I ϵ ((1 / 2 : ℝ) ^ r) := by
    unfold gN
    rw [length_flatMap_uniform _ _ (numTypes I ϵ ((1 / 2 : ℝ) ^ r))
      (fun _ => by rw [List.length_map, List.length_finRange]), List.length_finRange]
  rw [← hlen]
  refine forall₂_replicate _ _ fun y hy => ?_
  unfold gN at hy
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hy
  obtain ⟨i, t, rfl⟩ := hy
  exact wN_mem I ϵ r x hξ0 hξ1 i t

lemma gS_forall (hϵ : 0 < ϵ) :
    List.Forall₂ (fun a l => a ∈ l) (gS I ϵ r x) (sChoices I ϵ ((1 / 2 : ℝ) ^ r)) := by
  unfold gS sChoices
  refine forall₂_flatMap _ _ _ (fun i => forall₂_flatMap _ _ _ (fun d =>
    forall₂_map _ _ _ (fun t => ?_) _) _) _
  unfold vS
  split_ifs with h
  · unfold sGrid
    simp only [List.mem_map]
    refine ⟨⌊min (Sip I ϵ ((1 / 2 : ℝ) ^ r) x i d t) 1 /
      (ϵ / (numTypes I ϵ ((1 / 2 : ℝ) ^ r) : ℝ))⌋₊, ?_, rfl⟩
    simp
    generalize numTypes I ϵ (2 ^ r)⁻¹ = T
    apply Nat.floor_le_floor
    calc min (Sip I ϵ ((1 / 2) ^ r) x i d t) 1 / (ϵ / T) ≤ 1 / (ϵ / T) :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = T / ϵ := one_div_div _ _
  · simp

lemma induced {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    IsInducedGuess I ϵ ((1 / 2 : ℝ) ^ r) ξ x (fun i t => (nAt (gN I ϵ ξ r x) i t).1)
      (fun i t => (nAt (gN I ϵ ξ r x) i t).2) (fun i d t => sAt (gS I ϵ r x) i d t) where
  exact i t h := by
    simp only [nAt_gN]; unfold wN; rw [if_pos h]; exact ⟨rfl, rfl⟩
  approx i t h := by
    simp only [nAt_gN]; unfold wN; rw [if_neg (not_le.2 h)]
    have hpos : (0 : ℝ) < Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t := lt_trans (by positivity) h
    have hN : 1 ≤ Nip I ϵ ((1 / 2 : ℝ) ^ r) x i t := by exact_mod_cast hpos
    obtain ⟨h1, h2⟩ := kOf_spec hξ0 hξ1 _ hN
    refine ⟨?_, h1, by exact_mod_cast h2⟩
    rw [one_div_half_pow]; push_cast; rfl
  small i d hd t ht := by
    simp only [sAt_gS]; unfold vS; rw [if_pos ⟨hd, ht⟩]

end Guess

/-! ## Success probability -/

lemma prGE_pure_good {β : Type} {G : β → Prop} (b : β) (hb : G b) (c : ENNReal) (hc : c ≤ 1) :
    PrGE (pure b : Prog β) G c := by
  intro s
  rw [run_pure', (PMF.toOuterMeasure_apply_eq_one_iff _ _).2]
  · exact hc
  · rw [PMF.support_pure]; intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hb

lemma pmf_bind_def {α β : Type} (p : PMF α) (f : α → PMF β) : p >>= f = p.bind f := rfl

lemma callRnd_bind_ge {β : Type} (rnd : Rounding) (P : LPData) (y : P.Vars)
    (f : Assignment P.m P.n → Prog β) (s : Cost) (A : Set (Assignment P.m P.n)) (S : Set (β × Cost))
    (h : ∀ X ∈ (rnd P y).support, X ∈ A → ∀ s', ((f X).run s').support ⊆ S) :
    (rnd P y).toOuterMeasure A ≤ ((callRnd rnd P y >>= f).run s).toOuterMeasure S := by
  rw [StateT.run_bind, run_callRnd, pmf_bind_def, PMF.bind_bind]
  refine pmf_bind_ge2 _ _ _ _ fun X hX hXA => ?_
  rw [PMF.pure_bind]
  exact h X hX hXA _

lemma half_le_one : ENNReal.ofReal (1 / 2) ≤ 1 := ENNReal.ofReal_le_one.2 (by norm_num)

lemma santa_prob {m D n : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (I : SCInstance m D n)
    (lp : LPSolver) (rnd : Rounding) (hlp : IsLPSolver lp) (hrnd : IsDependentRounding rnd)
    (hIP : IPFeasible I) :
    PrGE (santaClaus ε I lp rnd) (Good I ε) (ENNReal.ofReal (1 / 2)) := by
  obtain ⟨x, hcard, hload⟩ := hIP
  have hξ0 : 0 < ε / 2 / 2 := by positivity
  have hξ1 : ε / 2 / 2 < 1 := by linarith
  simp only [santaClaus, opn, bind_assoc, pure_bind]
  refine prGE_tick_bind _ <| prGE_tick_bind _ <| prGE_tick_bind _ <| prGE_tick_bind _ <|
    prGE_tick_bind _ <| prGE_tick_bind _ <| prGE_tick_bind _ <| prGE_tick_bind _ <|
    prGE_foldProd _ (Inv I ε) (Good I ε) _ _ _
      (gN_forall I (ε / 2) (calib (ε / 2) m D) x hξ0 hξ1) ?_ ?_ ?_ none (by simp [Inv])
  · -- invariant
    intro b gN hb
    refine pres_foldProd _ _ _ ?_ _ hb
    intro b gS hb
    cases b with
    | some X => exact pres_pure _ hb
    | none =>
      dsimp only
      refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun o _ => ?_
      cases o with
      | none => exact pres_pure _ (by simp [Inv])
      | some y =>
        dsimp only
        refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun X _ =>
          pres_tick_bind _ (pres_pure _ ?_)
        intro X' hX'
        split_ifs at hX' with h
        cases hX'
        exact (check_iff I _ X).1 h
  · -- absorbing
    intro b gN hb
    refine pres_foldProd _ _ _ ?_ _ hb
    intro b gS hb
    cases b with
    | some X => exact pres_pure _ hb
    | none => exact absurd hb.2 (by simp [Good])
  · -- the induced guess
    intro b hb
    refine prGE_foldProd _ (Inv I ε) (Good I ε) _ _ _
      (gS_forall I (ε / 2) (calib (ε / 2) m D) x (by positivity)) ?_ ?_ ?_ b hb
    · intro b gS hb
      cases b with
      | some X => exact pres_pure _ hb
      | none =>
        dsimp only
        refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun o _ => ?_
        cases o with
        | none => exact pres_pure _ (by simp [Inv])
        | some y =>
          dsimp only
          refine pres_bind (Q := fun _ => True) (fun _ _ _ => trivial) fun X _ =>
            pres_tick_bind _ (pres_pure _ ?_)
          intro X' hX'
          split_ifs at hX' with h
          cases hX'
          exact (check_iff I _ X).1 h
    · intro b gS hb
      cases b with
      | some X => exact pres_pure _ hb
      | none => exact absurd hb.2 (by simp [Good])
    · intro b hb
      cases b with
      | some X => exact prGE_pure_good _ ⟨X, rfl, hb X rfl⟩ _ half_le_one
      | none =>
        dsimp only
        intro s
        set r := calib (ε / 2) m D with hr
        have hr0 : r ≠ 0 := by rw [hr, calib]; positivity
        have hδ0 : (0 : ℝ) < (1 / 2) ^ r := by positivity
        have hδ1 : (1 / 2 : ℝ) ^ r < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hr0
        have hg := induced I (ε / 2) r x hξ0 hξ1
        have hfeas := lemma_2_2 I (ε / 2) ((1 / 2 : ℝ) ^ r) (ε / 2 / 2) (by positivity) hδ0 hδ1
          ⟨2 ^ r, by rw [one_div_half_pow]; push_cast; rfl⟩ hξ0.le (by linarith) x hcard hload
          _ _ _ hg
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (hlp.complete _ ⟨_, hfeas⟩)
        have hyF := hlp.sound _ y hy
        rw [StateT.run_bind, run_callLP, pmf_bind_def, PMF.pure_bind]
        dsimp only
        rw [hy]
        dsimp only
        refine le_trans ?_ (callRnd_bind_ge rnd _ y _ _ {Y | LoadAtLeast I Y (1 - ε)} _ ?_)
        · have h := lemma_2_3 I (ε / 2) ((1 / 2 : ℝ) ^ r) (by positivity) (by linarith) hδ0 hδ1
            (fun hpos => delta_calibration I (ε / 2) (by positivity) (by linarith) hpos)
            x hload _ _ _ hg y hyF rnd hrnd
          have e : (1 : ℝ) - 2 * (ε / 2) = 1 - ε := by ring
          rw [e] at h
          exact ENNReal.ofReal_le_of_le_toReal h
        · intro X hX hL s' z hz
          rw [run_tick_bind, run_pure', PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          have hmc := constraints_I_III I (ε / 2) ((1 / 2 : ℝ) ^ r) (ε / 2 / 2) x hcard _ _ _ hg y
            hyF.1 rnd hrnd X hX
          have hchk : check I (1 - ε) X = true := (check_iff I _ X).2 ⟨hmc, hL⟩
          simp only [hchk, if_true, Set.mem_ofPred_eq]
          exact ⟨X, rfl, hmc, hL⟩

lemma toOM_le_one {α : Type} (p : PMF α) (S : Set α) : p.toOuterMeasure S ≤ 1 := by
  rw [← (PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).2 (Set.subset_univ _)]
  exact MeasureTheory.measure_mono (Set.subset_univ _)

end FOSol

open FreeOrderEPTAS in
theorem solution :
    ∃ (f : ℕ → ℕ → ℕ → ℕ) (d : ℕ), ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (m D n : ℕ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding),
        IsLPSolver lp → IsDependentRounding rnd →
        (IPFeasible I → (1 / 2 : ℝ) ≤ pr ((santaClaus ε I lp rnd).run 0)
          {r | ∃ X, r.1 = some X ∧ MeetsCard I X ∧ LoadAtLeast I X (1 - ε)}) ∧
        ∀ r ∈ ((santaClaus ε I lp rnd).run 0).support,
          (∀ X, r.1 = some X → MeetsCard I X ∧ LoadAtLeast I X (1 - ε)) ∧
          r.2.total ≤ f ⌈1 / ε⌉₊ m D * (n + 1) ^ d ∧
          r.2.maxSize ≤ f ⌈1 / ε⌉₊ m D * (n + 1) := by
  refine ⟨fun q m D => FOSol.Cb q m D + 6 * (m + 1) * (D + 2), 2, ?_⟩
  intro ε hε0 hε1 m D n I lp rnd hlp hrnd
  refine ⟨fun hIP => ?_, fun r hr => ?_⟩
  · have h := FOSol.santa_prob ε hε0 hε1 I lp rnd hlp hrnd hIP 0
    unfold pr
    have hne := ne_top_of_le_ne_top ENNReal.one_ne_top
      (FOSol.toOM_le_one ((santaClaus ε I lp rnd).run 0) {r | FOSol.Good I ε r.1})
    have := ENNReal.toReal_mono hne h
    rw [ENNReal.toReal_ofReal (by norm_num)] at this
    exact this
  · refine ⟨FOSol.santa_pres ε I lp rnd 0 r hr, ?_⟩
    have hc := FOSol.santa_cost ε I lp rnd 0 (Nat.zero_le _) r hr
    have hK := FOSol.Kx_le hε0 hε1 (q := ⌈1 / ε⌉₊) rfl I
    have h0 : (0 : Cost).total = 0 := rfl
    rw [h0, zero_add] at hc
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, ?_⟩
    · refine h1.trans (hK.trans ?_)
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · refine h2.trans ?_
      have : 6 * (m + 1) * (D + 2) ≤ FOSol.Cb ⌈1 / ε⌉₊ m D + 6 * (m + 1) * (D + 2) :=
        Nat.le_add_left _ _
      exact Nat.mul_le_mul_right _ this
