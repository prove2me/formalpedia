-- Prove2me | solution 1 for CostScaling.StrongPoly.strongly_polynomial_iterations_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:05:25.823397+00:00
-- url     : https://prove2.me/submissions/d7312be7-38dc-4c37-8889-6cd43fd9ed27

import Mathlib
import Definitions.Def_CostScaling_StrongPoly_IsHalvingRun

set_option autoImplicit false

namespace CSb2927065

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Layers of vertices reachable from `w` along arcs with `h > 0`. -/
noncomputable def layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) : ℕ → Finset V
  | 0 => {w}
  | k + 1 => layer N h w k ∪
      Finset.univ.filter (fun y => ∃ x ∈ layer N h w k, (x, y) ∈ N.E ∧ 0 < h x y)

lemma layer_succ_sub (N : CircNetwork V) (h : V → V → ℝ) (w : V) (k : ℕ) :
    layer N h w k ⊆ layer N h w (k + 1) := by
  show layer N h w k ⊆ layer N h w k ∪ _
  exact Finset.subset_union_left

lemma w_mem_layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∀ k : ℕ, w ∈ layer N h w k := by
  intro k
  induction k with
  | zero => simp [layer]
  | succ k ih => exact layer_succ_sub N h w k ih

lemma layer_bound (N : CircNetwork V) (h : V → V → ℝ) (w : V) (q : V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε) :
    ∀ k : ℕ, ∀ x ∈ layer N h w k, q x ≤ q w + 2 * (k : ℝ) * ε := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp [layer] at hx
    subst hx
    simp
  | succ k ih =>
    intro x hx
    have hx' : x ∈ layer N h w k ∪
        Finset.univ.filter (fun y => ∃ z ∈ layer N h w k, (z, y) ∈ N.E ∧ 0 < h z y) := hx
    rcases Finset.mem_union.mp hx' with h1 | h1
    · have := ih x h1
      push_cast
      nlinarith
    · obtain ⟨z, hz, hzE, hzpos⟩ := (Finset.mem_filter.mp h1).2
      have := ih z hz
      have := hstep z x hzE hzpos
      push_cast
      nlinarith

lemma layer_stab (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∃ k : ℕ, k + 1 ≤ Fintype.card V ∧ layer N h w (k + 1) ⊆ layer N h w k := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, k ≤ Fintype.card V → k + 1 ≤ (layer N h w k).card := by
    intro k
    induction k with
    | zero => intro _; simp [layer]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hss : layer N h w k ⊂ layer N h w (k + 1) :=
        HasSubset.Subset.ssubset_of_not_subset (layer_succ_sub N h w k) (hcon k hk)
      have := Finset.card_lt_card hss
      omega
  have := key (Fintype.card V) le_rfl
  have := Finset.card_le_univ (layer N h w (Fintype.card V))
  omega

lemma cut_false (N : CircNetwork V) (h : V → V → ℝ) (S : Finset V)
    (hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a)
    (hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0)
    (hclosed : ∀ a ∈ S, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ S)
    (v w : V) (hw : w ∈ S) (hv : v ∉ S) (hvw : (v, w) ∈ N.E) (hpos : 0 < h v w) : False := by
  classical
  let φ : V → V → ℝ := fun x y => if (x, y) ∈ N.E then h y x else 0
  have hφanti : ∀ x y, φ x y = -φ y x := by
    intro x y
    simp only [φ]
    by_cases hxy : (x, y) ∈ N.E
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      rw [if_pos hxy, if_pos hyx]
      exact hanti y x hyx
    · have hyx : (y, x) ∉ N.E := fun h' => hxy ((N.symm y x).1 h')
      rw [if_neg hxy, if_neg hyx]
      simp
  have htot : ∑ x ∈ S, ∑ y, φ x y = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hcons x, Finset.sum_filter]
  have hA : ∑ x ∈ S, ∑ y ∈ S, φ x y = 0 := by
    have h1 : ∑ x ∈ S, ∑ y ∈ S, φ x y = ∑ y ∈ S, ∑ x ∈ S, φ x y := Finset.sum_comm
    have h2 : ∑ y ∈ S, ∑ x ∈ S, φ x y = -∑ y ∈ S, ∑ x ∈ S, φ y x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hφanti x y
    linarith
  have hnn : ∀ x ∈ S, ∀ y ∈ Sᶜ, 0 ≤ φ x y := by
    intro x hx y hy
    simp only [φ]
    split_ifs with hxy
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      have hle : ¬ 0 < h x y := fun hp => (Finset.mem_compl.mp hy) (hclosed x hx y hxy hp)
      push_neg at hle
      rw [hanti y x hyx]
      linarith
    · exact le_rfl
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  have hB : 0 < ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    have hv' : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    have e1 : φ w v ≤ ∑ y ∈ Sᶜ, φ w y :=
      Finset.single_le_sum (fun y hy => hnn w hw y hy) hv'
    have e2 : ∑ y ∈ Sᶜ, φ w y ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y :=
      Finset.single_le_sum (f := fun x => ∑ y ∈ Sᶜ, φ x y)
        (fun x hx => Finset.sum_nonneg (fun y hy => hnn x hx y hy)) hw
    have e0 : φ w v = h v w := by simp only [φ]; rw [if_pos hwv]
    linarith
  have hsplit : ∑ x ∈ S, ∑ y, φ x y =
      ∑ x ∈ S, ∑ y ∈ S, φ x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_add_sum_compl]
  linarith



/-- consecutive pairs of a list -/
def pA : List V → List (V × V)
  | a :: b :: l => (a, b) :: pA (b :: l)
  | _ => []

theorem pA_split (l1 : List V) (x : V) (l2 : List V) :
    pA (l1 ++ x :: l2) = pA (l1 ++ [x]) ++ pA (x :: l2) := by
  induction l1 with
  | nil => simp [pA]
  | cons a l1 ih =>
    cases l1 with
    | nil => simp [pA]
    | cons b l1 =>
      simp only [List.cons_append, pA] at ih ⊢
      rw [ih]

theorem zip_pA (L : List V) (x y : V) :
    List.zip (x :: L) (L ++ [y]) = pA (x :: (L ++ [y])) := by
  induction L generalizing x with
  | nil => simp [pA]
  | cons b L ih =>
    simp only [List.cons_append, List.zip_cons_cons, pA]
    rw [← ih]

theorem cycleArcs_cons (x : V) (L : List V) :
    cycleArcs (x :: L) = pA (x :: (L ++ [x])) := by
  unfold cycleArcs
  rw [List.rotate_cons_succ, List.rotate_zero, zip_pA]



/-- cost of a path given as a vertex list -/
noncomputable def pathCost (c : V → V → ℝ) (P : List V) : ℝ :=
  ((pA P).map (fun a => c a.1 a.2)).sum

def Res (N : CircNetwork V) (f : V → V → ℝ) (P : List V) : Prop :=
  ∀ a ∈ pA P, a ∈ N.E ∧ 0 < resCap N f a.1 a.2

def S (N : CircNetwork V) (f : V → V → ℝ) (v : V) : Set (List V) :=
  {Q | (Q ++ [v]).Nodup ∧ Res N f (Q ++ [v])}

theorem S_finite (N : CircNetwork V) (f : V → V → ℝ) (v : V) : (S N f v).Finite := by
  refine (List.finite_length_le V (Fintype.card V)).subset (fun Q hQ => ?_)
  have := hQ.1.length_le_card
  simp only [List.length_append, List.length_singleton] at this
  show Q.length ≤ Fintype.card V
  omega

theorem pA_snoc2 (Q : List V) (v w : V) : pA ((Q ++ [v]) ++ [w]) = pA (Q ++ [v]) ++ [(v, w)] := by
  have : (Q ++ [v]) ++ [w] = Q ++ v :: [w] := by simp
  rw [this, pA_split]; simp [pA]

theorem exists_pot (N : CircNetwork V) (f : V → V → ℝ) (c : V → V → ℝ)
    (hneg : ∀ Γ : List V, IsResidualCycle N f Γ →
      0 ≤ ((cycleArcs Γ).map (fun a => c a.1 a.2)).sum) :
    ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → p w ≤ p v + c v w := by
  have hex : ∀ v, ∃ Q ∈ S N f v, ∀ Q' ∈ S N f v,
      pathCost c (Q ++ [v]) ≤ pathCost c (Q' ++ [v]) := by
    intro v
    refine Set.exists_min_image (S N f v) (fun Q => pathCost c (Q ++ [v])) (S_finite N f v)
      ⟨[], ?_, ?_⟩
    · simp
    · intro a ha; simp [pA] at ha
  choose Q hQ hmin using hex
  refine ⟨fun v => pathCost c (Q v ++ [v]), ?_⟩
  intro v w hvw hres
  dsimp only
  by_cases hw : w ∈ Q v ++ [v]
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hw
    have hsplit := pA_split A w B
    have hext : pA ((A ++ w :: B) ++ [w]) = pA (A ++ w :: B) ++ [(v, w)] := by
      rw [← hAB]; exact pA_snoc2 _ _ _
    have hext2 : pA ((A ++ w :: B) ++ [w]) = pA (A ++ [w]) ++ pA (w :: (B ++ [w])) := by
      have : (A ++ w :: B) ++ [w] = A ++ w :: (B ++ [w]) := by simp
      rw [this, pA_split]
    have hcyc : pA (w :: (B ++ [w])) = pA (w :: B) ++ [(v, w)] := by
      rw [hext, hsplit, List.append_assoc] at hext2
      exact (List.append_cancel_left hext2).symm
    have hnd : (A ++ w :: B).Nodup := hAB ▸ (hQ v).1
    have hR : Res N f (A ++ w :: B) := hAB ▸ (hQ v).2
    have hA : A ∈ S N f w := by
      refine ⟨?_, ?_⟩
      · have : A ++ w :: B = (A ++ [w]) ++ B := by simp
        rw [this] at hnd
        exact hnd.sublist (List.sublist_append_left _ _)
      · intro a ha; exact hR a (by rw [hsplit]; exact List.mem_append_left _ ha)
    have hcycle : IsResidualCycle N f (w :: B) := by
      refine ⟨List.cons_ne_nil _ _, hnd.sublist (List.sublist_append_right _ _), ?_⟩
      intro a ha
      rw [cycleArcs_cons, hcyc] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hR a (by rw [hsplit]; exact List.mem_append_right _ ha)
      · simp at ha; subst ha; exact ⟨hvw, hres⟩
    have hcost := hneg (w :: B) hcycle
    have hcc : ((cycleArcs (w :: B)).map (fun a => c a.1 a.2)).sum =
        pathCost c (w :: B) + c v w := by
      unfold pathCost; rw [cycleArcs_cons, hcyc]; simp
    have hpv : pathCost c (Q v ++ [v]) = pathCost c (A ++ [w]) + pathCost c (w :: B) := by
      unfold pathCost; rw [hAB, hsplit]; simp
    have := hmin w A hA
    linarith
  · have hS : Q v ++ [v] ∈ S N f w := by
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨(hQ v).1, List.nodup_singleton w, ?_⟩
        simp only [List.mem_singleton]
        rintro a ha b rfl rfl; exact hw ha
      · intro a ha
        rw [pA_snoc2] at ha
        rcases List.mem_append.mp ha with ha | ha
        · exact (hQ v).2 a ha
        · simp at ha; subst ha; exact ⟨hvw, hres⟩
    have := hmin w _ hS
    have e : pathCost c ((Q v ++ [v]) ++ [w]) = pathCost c (Q v ++ [v]) + c v w := by
      unfold pathCost; rw [pA_snoc2]; simp
    linarith



/-- the potential argument: sum of potential differences against a circulation difference -/
theorem pot_zero (N : CircNetwork V) (h : V → V → ℝ) (p : V → ℝ)
    (hanti : ∀ v w, (v, w) ∈ N.E → h v w = -h w v)
    (hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), h v w = 0) :
    ∑ a ∈ N.E, (p a.1 - p a.2) * h a.1 a.2 = 0 := by
  have hE : ∀ F : V × V → ℝ, ∑ a ∈ N.E, F a =
      ∑ x, ∑ y, if (x, y) ∈ N.E then F (x, y) else 0 := by
    intro F
    rw [← Fintype.sum_prod_type (fun a => if a ∈ N.E then F a else 0)]
    rw [Finset.sum_ite_mem]; simp
  have A : ∀ x, ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) = 0 := by
    intro x
    have : ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) =
        - p x * ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs with hy
      · rw [hanti x y hy]; ring
      · rfl
    rw [this, hcons x, mul_zero]
  have B : ∀ y, ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) = 0 := by
    intro y
    have : ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) =
        p y * ∑ x ∈ Finset.univ.filter (fun x => (y, x) ∈ N.E), h x y := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hxy : (x, y) ∈ N.E
      · simp [hxy, (N.symm x y).mp hxy]
      · have : (y, x) ∉ N.E := fun h' => hxy ((N.symm y x).mp h')
        simp [hxy, this]
    rw [this, hcons y, mul_zero]
  rw [hE]
  dsimp only
  calc ∑ x, ∑ y, (if (x, y) ∈ N.E then (p x - p y) * h x y else 0)
      = ∑ x, ∑ y, (if (x, y) ∈ N.E then p x * h x y else 0) -
          ∑ y, ∑ x, (if (x, y) ∈ N.E then p y * h x y else 0) := by
        rw [Finset.sum_comm (f := fun y x => if (x, y) ∈ N.E then p y * h x y else 0)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> ring
    _ = 0 := by simp [A, B]


theorem lsum_add {α : Type*} (A : List α) (P Q : α → ℝ) :
    (A.map (fun a => P a + Q a)).sum = (A.map P).sum + (A.map Q).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_sub {α : Type*} (A : List α) (P Q : α → ℝ) :
    (A.map (fun a => P a - Q a)).sum = (A.map P).sum - (A.map Q).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_const {α : Type*} (A : List α) (d : ℝ) :
    (A.map (fun _ => d)).sum = A.length * d := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

theorem lsum_ge {α : Type*} (A : List α) (r : α → ℝ) (b : ℝ) (h : ∀ a ∈ A, b ≤ r a) :
    A.length * b ≤ (A.map r).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    push_cast
    linarith

theorem lsum_avg {α : Type*} (A : List α) (r : α → ℝ) (b : ℝ) (hne : A ≠ [])
    (hs : (A.map r).sum ≤ A.length * b) : ∃ a ∈ A, r a ≤ b := by
  by_contra hno
  push_neg at hno
  cases A with
  | nil => exact hne rfl
  | cons a A =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hs
    have h1 := hno a (by simp)
    have h2 := lsum_ge A r b (fun x hx => (hno x (by simp [hx])).le)
    push_cast at hs
    linarith

theorem len_arcs (Γ : List V) : (cycleArcs Γ).length = Γ.length := by
  unfold cycleArcs; simp

theorem arcs_sum_pot (Γ : List V) (p : V → ℝ) :
    ((cycleArcs Γ).map (fun a => p a.1 - p a.2)).sum = 0 := by
  unfold cycleArcs
  rw [lsum_sub]
  have h1 : (Γ.zip (Γ.rotate 1)).map (fun a => p a.1) = Γ.map p := by
    rw [show (fun a : V × V => p a.1) = p ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp)]
  have h2 : (Γ.zip (Γ.rotate 1)).map (fun a => p a.2) = (Γ.rotate 1).map p := by
    rw [show (fun a : V × V => p a.2) = p ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp)]
  rw [h1, h2, ((List.rotate_perm Γ 1).map p).sum_eq, sub_self]

theorem cyc_rc (N : CircNetwork V) (Γ : List V) (p : V → ℝ) :
    ((cycleArcs Γ).map (fun a => reducedCost N p a.1 a.2)).sum = cycleCost N Γ := by
  unfold cycleCost reducedCost
  have : (fun a : V × V => N.c a.1 a.2 + p a.1 - p a.2) =
      fun a => N.c a.1 a.2 + (p a.1 - p a.2) := by funext a; ring
  rw [this, lsum_add, arcs_sum_pot, add_zero]

theorem cyc_lower (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) (hf : IsEpsOptimal N f ε)
    (Γ : List V) (hΓ : IsResidualCycle N f Γ) : -ε * Γ.length ≤ cycleCost N Γ := by
  obtain ⟨-, -, p, hp⟩ := hf
  rw [← cyc_rc N Γ p]
  have := lsum_ge (cycleArcs Γ) (fun a => reducedCost N p a.1 a.2) (-ε)
    (fun a ha => hp a.1 a.2 (hΓ.2.2 a ha).1 (hΓ.2.2 a ha).2)
  rw [len_arcs] at this
  linarith

theorem key (N : CircNetwork V) (f : V → V → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hf : IsCirculation N f)
    (h : ∀ Γ, IsResidualCycle N f Γ → -δ * Γ.length ≤ cycleCost N Γ) :
    IsEpsOptimal N f δ := by
  obtain ⟨p, hp⟩ := exists_pot N f (fun v w => N.c v w + δ) (by
    intro Γ hΓ
    have h1 := h Γ hΓ
    have e : ((cycleArcs Γ).map (fun a => N.c a.1 a.2 + δ)).sum =
        cycleCost N Γ + Γ.length * δ := by
      unfold cycleCost
      rw [lsum_add, lsum_const, len_arcs]
    rw [e]
    linarith)
  refine ⟨hf, hδ, p, ?_⟩
  intro v w hvw hres
  have := hp v w hvw hres
  unfold reducedCost
  linarith

theorem eps_nonempty (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    ∃ ε, IsEpsOptimal N f ε := by
  refine ⟨∑ a ∈ N.E, |N.c a.1 a.2|, hf, Finset.sum_nonneg (fun a _ => abs_nonneg _), fun _ => 0, ?_⟩
  intro v w hvw _
  have h1 := Finset.single_le_sum (f := fun a : V × V => |N.c a.1 a.2|)
    (fun a _ => abs_nonneg _) hvw
  have h2 := neg_abs_le (N.c v w)
  unfold reducedCost
  simp only at h1 ⊢
  linarith

theorem eps_bdd (N : CircNetwork V) (f : V → V → ℝ) :
    BddBelow {ε : ℝ | IsEpsOptimal N f ε} := ⟨0, fun _ h => h.2.1⟩

theorem epsOpt_le (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) (h : IsEpsOptimal N f ε) :
    epsOpt N f ≤ ε := csInf_le (eps_bdd N f) h

theorem epsOpt_nonneg (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    0 ≤ epsOpt N f := le_csInf (eps_nonempty N f hf) (fun _ h => h.2.1)

theorem cyc_ge (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsResidualCycle N f Γ) : -epsOpt N f * Γ.length ≤ cycleCost N Γ := by
  have hl : (0 : ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
  have : -cycleCost N Γ / Γ.length ≤ epsOpt N f := by
    apply le_csInf (eps_nonempty N f hf)
    intro ε hε
    have := cyc_lower N f ε hε Γ hΓ
    rw [div_le_iff₀ hl]
    linarith
  rw [div_le_iff₀ hl] at this
  linarith

theorem attain (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsEpsOptimal N f (epsOpt N f) :=
  key N f _ (epsOpt_nonneg N f hf) hf (cyc_ge N f hf)

theorem tight (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (hpos : 0 < epsOpt N f) :
    ∃ Γ, IsResidualCycle N f Γ ∧ cycleCost N Γ ≤ -epsOpt N f * Γ.length := by
  by_contra hno
  push_neg at hno
  let T : Set (List V) := {Γ | IsResidualCycle N f Γ}
  have hT : T.Finite := by
    refine (List.finite_length_le V (Fintype.card V)).subset (fun Γ hΓ => ?_)
    exact hΓ.2.1.length_le_card
  let r : List V → ℝ := fun Γ => -cycleCost N Γ / Γ.length
  have hr : ∀ Γ ∈ T, r Γ < epsOpt N f := by
    intro Γ hΓ
    have hl : (0 : ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
    have := hno Γ hΓ
    show -cycleCost N Γ / Γ.length < epsOpt N f
    rw [div_lt_iff₀ hl]
    linarith
  obtain ⟨δ, hδ0, hδlt, hδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < epsOpt N f ∧ ∀ Γ ∈ T, r Γ ≤ δ := by
    by_cases hne : T.Nonempty
    · obtain ⟨Γ0, h0, hmax⟩ := Set.exists_max_image T r hT hne
      exact ⟨max 0 (r Γ0), le_max_left _ _, max_lt hpos (hr Γ0 h0),
        fun Γ hΓ => (hmax Γ hΓ).trans (le_max_right _ _)⟩
    · exact ⟨0, le_rfl, hpos, fun Γ hΓ => absurd ⟨Γ, hΓ⟩ hne⟩
  have hopt := key N f δ hδ0 hf (by
    intro Γ hΓ
    have hl : (0 : ℝ) < Γ.length := by exact_mod_cast List.length_pos_of_ne_nil hΓ.1
    have := hδ Γ hΓ
    simp only [r] at this
    rw [div_le_iff₀ hl] at this
    linarith)
  have := epsOpt_le N f δ hopt
  linarith

lemma fixres (N : CircNetwork V) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (hηε : 2 * (Fintype.card V : ℝ) * ε ≤ η) (f : V → V → ℝ)
    (hf : IsCirculation N f) (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V)
    (hvw : (v, w) ∈ N.E) (hneg : reducedCost N p v w ≤ -η)
    (g : V → V → ℝ) (hg : IsEpsOptimal N g ε) : resCap N g v w ≤ 0 := by
  obtain ⟨hgc, -, p', hgp⟩ := hg
  haveI : Nonempty V := ⟨v⟩
  have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hnε : 1 * ε ≤ (Fintype.card V : ℝ) * ε := mul_le_mul_of_nonneg_right hn hε
  have hfu : N.u v w ≤ f v w := by
    by_contra hlt
    push_neg at hlt
    have := hfp v w hvw (by unfold resCap; linarith)
    have hε0 : ε = 0 := le_antisymm (by linarith) hε
    subst hε0
    linarith
  by_contra hres
  push_neg at hres
  have hlt : g v w < f v w := by unfold resCap at hres; linarith
  let h : V → V → ℝ := fun a b => f a b - g a b
  let q : V → ℝ := fun x => p' x - p x
  have hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε := by
    intro a b hab hpos
    have hba := (N.symm a b).1 hab
    simp only [h] at hpos
    have h1 := hgp a b hab (by unfold resCap; linarith [hf.1 a b hab])
    have h2 := hfp b a hba (by
      unfold resCap
      linarith [hf.2.1 a b hab, hgc.2.1 a b hab, hgc.1 b a hba])
    have h3 := N.cost_antisymm a b hab
    unfold reducedCost at h1 h2
    simp only [q]
    linarith
  have hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a := by
    intro a b hab
    simp only [h]
    rw [hf.2.1 a b hab, hgc.2.1 a b hab]
    ring
  have hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0 := by
    intro x
    simp only [h]
    rw [Finset.sum_sub_distrib, hf.2.2 x, hgc.2.2 x]
    ring
  obtain ⟨k, hk, hsub⟩ := layer_stab N h w
  have hclosed : ∀ a ∈ layer N h w k, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ layer N h w k := by
    intro a ha b hab hp
    apply hsub
    show b ∈ layer N h w k ∪ _
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, hab, hp⟩
  have hwS : w ∈ layer N h w k := w_mem_layer N h w k
  have hvS : v ∈ layer N h w k := by
    by_contra hvS
    exact cut_false N h (layer N h w k) hanti hcons hclosed v w hwS hvS hvw
      (by simp only [h]; linarith)
  have hqv := layer_bound N h w q ε hε hstep k v hvS
  have hg1 := hgp v w hvw hres
  have hkR : ((k : ℝ) + 1) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hk
  have hkε : (k : ℝ) * ε ≤ ((Fintype.card V : ℝ) - 1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε
  unfold reducedCost at hneg hg1
  simp only [q] at hqv
  have hkey : η ≤ 2 * (k : ℝ) * ε + ε := by linarith
  have hε0 : ε = 0 := le_antisymm (by linarith) hε
  subst hε0
  simp at hkey
  linarith

noncomputable def Sset (N : CircNetwork V) (ε : ℝ) : Finset (V × V) :=
  @Finset.filter _ (fun a => ∀ g : V → V → ℝ, IsEpsOptimal N g ε → resCap N g a.1 a.2 ≤ 0)
    (Classical.decPred _) N.E

theorem mem_Sset (N : CircNetwork V) (ε : ℝ) (a : V × V) :
    a ∈ Sset N ε ↔ a ∈ N.E ∧ ∀ g : V → V → ℝ, IsEpsOptimal N g ε → resCap N g a.1 a.2 ≤ 0 := by
  unfold Sset
  simp only [Finset.mem_filter]

theorem Sset_mono (N : CircNetwork V) (ε ε' : ℝ) (h0 : 0 ≤ ε') (hle : ε' ≤ ε) :
    Sset N ε ⊆ Sset N ε' := by
  intro a ha
  rw [mem_Sset] at ha ⊢
  refine ⟨ha.1, fun g hg => ha.2 g ⟨hg.1, by linarith, ?_⟩⟩
  obtain ⟨-, -, p, hp⟩ := hg
  exact ⟨p, fun v w hvw hr => le_trans (by linarith) (hp v w hvw hr)⟩

theorem step (N : CircNetwork V) (f f' : V → V → ℝ) (hf : IsCirculation N f)
    (hf' : IsCirculation N f') (hpos : 0 < epsOpt N f)
    (h2n : 2 * (Fintype.card V : ℝ) * epsOpt N f' ≤ epsOpt N f) :
    ∃ a ∈ Sset N (epsOpt N f'), a ∉ Sset N (epsOpt N f) := by
  obtain ⟨Γ, hΓ, hcost⟩ := tight N f hf hpos
  obtain ⟨-, -, p', hp'⟩ := attain N f' hf'
  have hs : ((cycleArcs Γ).map (fun a => reducedCost N p' a.1 a.2)).sum ≤
      (cycleArcs Γ).length * (-epsOpt N f) := by
    rw [cyc_rc, len_arcs]; linarith
  have hne : cycleArcs Γ ≠ [] := by
    intro h0
    have := len_arcs Γ
    rw [h0] at this
    exact hΓ.1 (List.length_eq_zero_iff.mp this.symm)
  obtain ⟨a, ha, hra⟩ := lsum_avg _ _ _ hne hs
  obtain ⟨haE, hares⟩ := hΓ.2.2 a ha
  refine ⟨a, ?_, ?_⟩
  · rw [mem_Sset]
    exact ⟨haE, fun g hg => fixres N (epsOpt N f') (epsOpt N f) (epsOpt_nonneg N f' hf') hpos
      h2n f' hf' p' hp' a.1 a.2 haE hra g hg⟩
  · intro hS
    rw [mem_Sset] at hS
    have := hS.2 f (attain N f hf)
    linarith

theorem notFull (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (hpos : 0 < epsOpt N f) : ∃ a ∈ N.E, a ∉ Sset N (epsOpt N f) := by
  obtain ⟨Γ, hΓ, -⟩ := tight N f hf hpos
  have hne : cycleArcs Γ ≠ [] := by
    intro h0
    have := len_arcs Γ
    rw [h0] at this
    exact hΓ.1 (List.length_eq_zero_iff.mp this.symm)
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨haE, hares⟩ := hΓ.2.2 a ha
  refine ⟨a, haE, fun hS => ?_⟩
  rw [mem_Sset] at hS
  have := hS.2 f (attain N f hf)
  linarith

theorem minCost (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (h0 : epsOpt N f = 0) : IsMinCost N f := by
  have hopt := attain N f hf
  rw [h0] at hopt
  obtain ⟨-, -, p, hp0⟩ := hopt
  have hp : ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → p w ≤ p v + N.c v w := by
    intro v w hvw hres
    have := hp0 v w hvw hres
    unfold reducedCost at this
    linarith
  refine ⟨hf, fun g hg => ?_⟩
  let h : V → V → ℝ := fun v w => g v w - f v w
  have hanti : ∀ v w, (v, w) ∈ N.E → h v w = -h w v := by
    intro v w hvw; show g v w - f v w = -(g w v - f w v)
    rw [hg.2.1 v w hvw, hf.2.1 v w hvw]; ring
  have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), h v w = 0 := by
    intro w; show ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), (g v w - f v w) = 0
    rw [Finset.sum_sub_distrib, hg.2.2 w, hf.2.2 w]; ring
  have hz := pot_zero N h p hanti hcons
  have hnn : 0 ≤ ∑ a ∈ N.E, (N.c a.1 a.2 + p a.1 - p a.2) * h a.1 a.2 := by
    refine Finset.sum_nonneg (fun a ha => ?_)
    obtain ⟨v, w⟩ := a
    show 0 ≤ (N.c v w + p v - p w) * (g v w - f v w)
    rcases lt_trichotomy (g v w) (f v w) with hlt | heq | hgt
    · have hwv : (w, v) ∈ N.E := (N.symm v w).mp ha
      have hres : 0 < resCap N f w v := by
        simp only [resCap]
        have := hg.1 w v hwv
        rw [hg.2.1 v w ha] at hlt; rw [hf.2.1 v w ha] at hlt
        linarith
      have := hp w v hwv hres
      rw [N.cost_antisymm w v hwv] at this
      nlinarith
    · rw [heq]; simp
    · have hres : 0 < resCap N f v w := by
        simp only [resCap]; linarith [hg.1 v w ha]
      have := hp v w ha hres
      nlinarith
  have hsplit : ∑ a ∈ N.E, (N.c a.1 a.2 + p a.1 - p a.2) * h a.1 a.2 =
      ∑ a ∈ N.E, N.c a.1 a.2 * h a.1 a.2 + ∑ a ∈ N.E, (p a.1 - p a.2) * h a.1 a.2 := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun a _ => ?_); ring
  have hdiff : ∑ a ∈ N.E, N.c a.1 a.2 * h a.1 a.2 =
      ∑ a ∈ N.E, N.c a.1 a.2 * g a.1 a.2 - ∑ a ∈ N.E, N.c a.1 a.2 * f a.1 a.2 := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun a _ => ?_)
    show N.c a.1 a.2 * (g a.1 a.2 - f a.1 a.2) = _; ring
  unfold cost
  linarith

theorem main_count (N : CircNetwork V) (hvertices : 2 ≤ Fintype.card V)
    (f : ℕ → V → V → ℝ) (hrun : CostScaling.StrongPoly.IsHalvingRun N f) :
    ∃ k : ℕ, k ≤ N.E.card * Nat.clog 2 (2 * Fintype.card V) ∧
      epsOpt N (f k) = 0 ∧ IsCirculation N (f k) := by
  set B := Nat.clog 2 (2 * Fintype.card V) with hB
  set m := N.E.card with hm
  by_contra H
  push_neg at H
  have C : ∀ k, k ≤ m * B → IsCirculation N (f k) ∧ 0 < epsOpt N (f k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hc := hrun.1
      exact ⟨hc, lt_of_le_of_ne (epsOpt_nonneg N _ hc) (fun h => H 0 hk h.symm hc)⟩
    | succ k ih =>
      intro hk
      obtain ⟨-, hpos⟩ := ih (by omega)
      have hopt := hrun.2 k hpos
      have hc := hopt.1
      exact ⟨hc, lt_of_le_of_ne (epsOpt_nonneg N _ hc) (fun h => H (k + 1) hk h.symm hc)⟩
  have D : ∀ k, k + 1 ≤ m * B → epsOpt N (f (k + 1)) ≤ epsOpt N (f k) / 2 := by
    intro k hk
    exact epsOpt_le N _ _ (hrun.2 k (C k (by omega)).2)
  have E : ∀ k j, k + j ≤ m * B → epsOpt N (f (k + j)) * 2 ^ j ≤ epsOpt N (f k) := by
    intro k j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hkj
      have h1 := ih (by omega)
      have h2 := D (k + j) (by omega)
      have h3 : 0 ≤ epsOpt N (f (k + (j + 1))) := (C _ hkj).2.le
      rw [show k + (j + 1) = k + j + 1 by omega] at h3 ⊢
      rw [pow_succ]
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) j]
  have h2B : (2 * Fintype.card V : ℝ) ≤ 2 ^ B := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * Fintype.card V)
    rw [← hB] at this
    exact_mod_cast this
  have F : ∀ j, j ≤ m → j ≤ (Sset N (epsOpt N (f (j * B)))).card := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hjB : j * B + B ≤ m * B := by
        have := Nat.mul_le_mul_right B hj
        rw [Nat.succ_mul] at this
        exact this
      have hidx : (j + 1) * B = j * B + B := by rw [Nat.succ_mul]
      rw [hidx]
      have hE := E (j * B) B hjB
      obtain ⟨hc0, hp0⟩ := C (j * B) (by omega)
      obtain ⟨hc1, hp1⟩ := C (j * B + B) hjB
      have h2n : 2 * (Fintype.card V : ℝ) * epsOpt N (f (j * B + B)) ≤ epsOpt N (f (j * B)) := by
        have := mul_le_mul_of_nonneg_left h2B hp1.le
        nlinarith
      have hle : epsOpt N (f (j * B + B)) ≤ epsOpt N (f (j * B)) := by
        have hn : (1 : ℝ) ≤ 2 * (Fintype.card V : ℝ) := by
          have : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hvertices
          linarith
        nlinarith
      have hsub := Sset_mono N _ _ hp1.le hle
      obtain ⟨a, ha1, ha0⟩ := step N _ _ hc0 hc1 hp0 h2n
      have hss : Sset N (epsOpt N (f (j * B))) ⊂ Sset N (epsOpt N (f (j * B + B))) :=
        HasSubset.Subset.ssubset_of_not_subset hsub (fun h => ha0 (h ha1))
      have := Finset.card_lt_card hss
      omega
  have hm' := F m le_rfl
  obtain ⟨hcm, hpm⟩ := C (m * B) le_rfl
  obtain ⟨a, haE, haS⟩ := notFull N _ hcm hpm
  have hsubE : Sset N (epsOpt N (f (m * B))) ⊆ N.E := by
    intro x hx; exact ((mem_Sset N _ x).mp hx).1
  have heq := Finset.eq_of_subset_of_card_le hsubE (by omega)
  exact haS (heq ▸ haE)

end CSb2927065

open CycleCanceling.MinMean in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (f : ℕ → V → V → ℝ) (hrun : CostScaling.StrongPoly.IsHalvingRun N f) :
    ∃ k : ℕ, k ≤ N.E.card * Nat.clog 2 (2 * Fintype.card V) ∧
      CycleCanceling.MinMean.epsOpt N (f k) = 0 ∧ IsMinCost N (f k) := by
  obtain ⟨k, hk, h0, hc⟩ := CSb2927065.main_count N hvertices f hrun
  exact ⟨k, hk, h0, CSb2927065.minCost N (f k) hc h0⟩
