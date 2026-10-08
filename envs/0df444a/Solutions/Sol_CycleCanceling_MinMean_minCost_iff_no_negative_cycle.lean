-- Prove2me | solution 1 for CycleCanceling.MinMean.minCost_iff_no_negative_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:25:50.216161+00:00
-- url     : https://prove2.me/submissions/fc6fb7db-7f33-4949-a32d-4e5a79b295f7

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

set_option autoImplicit false

namespace CCca456

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

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

theorem exists_delta {α : Type*} (L : List α) (r : α → ℝ) (h : ∀ a ∈ L, 0 < r a) :
    ∃ δ > 0, ∀ a ∈ L, δ ≤ r a := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
    obtain ⟨δ, hδ, hδL⟩ := ih (fun b hb => h b (by simp [hb]))
    refine ⟨min δ (r a), lt_min hδ (h a (by simp)), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδL b hb)

/-- the unit flow along a list of arcs -/
def dL (L : List (V × V)) (v w : V) : ℝ :=
  (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))).sum

theorem dL_antisymm (L : List (V × V)) (v w : V) : dL L v w = - dL L w v := by
  unfold dL
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

theorem dL_le_length (L : List (V × V)) (v w : V) : dL L v w ≤ L.length := by
  unfold dL
  have := List.sum_le_card_nsmul
    (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))) 1
    (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      split_ifs <;> norm_num)
  simpa using this

theorem dL_nonpos (L : List (V × V)) (v w : V) (h : (v, w) ∉ L) : dL L v w ≤ 0 := by
  unfold dL
  have := List.sum_le_card_nsmul
    (L.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then 1 else 0))) 0
    (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have : a ≠ (v, w) := fun e => h (e ▸ ha)
      split_ifs <;> simp_all)
  simpa using this

theorem dL_cost (N : CircNetwork V) (L : List (V × V)) (hL : ∀ a ∈ L, a ∈ N.E) :
    ∑ a ∈ N.E, N.c a.1 a.2 * dL L a.1 a.2 = 2 * (L.map (fun a => N.c a.1 a.2)).sum := by
  induction L with
  | nil => simp [dL]
  | cons b L ih =>
    have hb : b ∈ N.E := hL b (by simp)
    have ih' := ih (fun a ha => hL a (by simp [ha]))
    have hsplit : ∀ a : V × V, dL (b :: L) a.1 a.2 =
        ((if b = (a.1, a.2) then (1:ℝ) else 0) - (if b = (a.2, a.1) then 1 else 0)) +
          dL L a.1 a.2 := by
      intro a; simp [dL]
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib, ih', mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ a ∈ N.E, N.c a.1 a.2 * (if b = (a.1, a.2) then (1:ℝ) else 0) = N.c b.1 b.2 := by
      simp only [Prod.mk.eta, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq N.E b]; simp [hb]
    have e2 : ∑ a ∈ N.E, N.c a.1 a.2 * (if b = (a.2, a.1) then (1:ℝ) else 0) = - N.c b.1 b.2 := by
      have : ∀ a : V × V, (b = (a.2, a.1)) ↔ (a = b.swap) := by
        intro a; constructor
        · rintro rfl; simp
        · rintro rfl; simp
      simp only [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' N.E b.swap]
      have hs : b.swap ∈ N.E := by
        have := (N.symm b.1 b.2).mp (by simpa using hb); simpa [Prod.swap] using this
      simp only [hs, if_true, Prod.fst_swap, Prod.snd_swap]
      rw [N.cost_antisymm b.2 b.1 (by simpa [Prod.swap] using hs)]
    rw [e1, e2]; simp; ring

theorem dL_div (N : CircNetwork V) (L : List (V × V)) (hL : ∀ a ∈ L, a ∈ N.E) (w : V) :
    ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), dL L v w =
      (L.map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum := by
  induction L with
  | nil => simp [dL]
  | cons b L ih =>
    have hb : b ∈ N.E := hL b (by simp)
    have ih' := ih (fun a ha => hL a (by simp [ha]))
    have hsplit : ∀ v, dL (b :: L) v w =
        ((if b = (v, w) then (1:ℝ) else 0) - (if b = (w, v) then 1 else 0)) + dL L v w := by
      intro v; simp [dL]
    simp_rw [hsplit, Finset.sum_add_distrib, ih', Finset.sum_sub_distrib]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    obtain ⟨x, y⟩ := b
    simp only [Prod.mk.injEq]
    congr 1
    · by_cases hy : y = w
      · subst hy
        have hx : (y, x) ∈ N.E := (N.symm x y).mp hb
        rw [Finset.sum_eq_single x]
        · simp [hx]
        · intro v _ hv; simp [Ne.symm hv]
        · intro hx'; simp [hx] at hx'
      · simp [hy]
    · by_cases hx : x = w
      · subst hx
        rw [Finset.sum_eq_single y]
        · simp [hb]
        · intro v _ hv; simp [Ne.symm hv]
        · intro hy'; simp [hb] at hy'
      · simp [hx]

theorem cycle_div (Γ : List V) (w : V) :
    ((cycleArcs Γ).map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum
      = 0 := by
  have hlen : Γ.length = (Γ.rotate 1).length := by simp
  have h1 : (cycleArcs Γ).map Prod.fst = Γ := by
    unfold cycleArcs; exact List.map_fst_zip (le_of_eq hlen)
  have h2 : (cycleArcs Γ).map Prod.snd = Γ.rotate 1 := by
    unfold cycleArcs; exact List.map_snd_zip (le_of_eq hlen.symm)
  have hs : ∀ (L : List (V × V)),
      (L.map (fun a => (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then 1 else 0))).sum =
      ((L.map Prod.snd).map (fun x => if x = w then (1:ℝ) else 0)).sum -
      ((L.map Prod.fst).map (fun x => if x = w then (1:ℝ) else 0)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  rw [hs, h1, h2]
  have := ((List.rotate_perm Γ 1).map (fun x => if x = w then (1:ℝ) else 0)).sum_eq
  rw [this]; ring

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

/-- cost of a path given as a vertex list -/
noncomputable def pathCost (N : CircNetwork V) (P : List V) : ℝ :=
  ((pA P).map (fun a => N.c a.1 a.2)).sum

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

theorem exists_pot (N : CircNetwork V) (f : V → V → ℝ)
    (hneg : ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycleCost N Γ < 0) :
    ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → p w ≤ p v + N.c v w := by
  have hex : ∀ v, ∃ Q ∈ S N f v, ∀ Q' ∈ S N f v,
      pathCost N (Q ++ [v]) ≤ pathCost N (Q' ++ [v]) := by
    intro v
    refine Set.exists_min_image (S N f v) (fun Q => pathCost N (Q ++ [v])) (S_finite N f v)
      ⟨[], ?_, ?_⟩
    · simp
    · intro a ha; simp [pA] at ha
  choose Q hQ hmin using hex
  refine ⟨fun v => pathCost N (Q v ++ [v]), ?_⟩
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
    have hcost : 0 ≤ cycleCost N (w :: B) := by
      by_contra hc; exact hneg ⟨w :: B, hcycle, lt_of_not_ge hc⟩
    have hcc : cycleCost N (w :: B) = pathCost N (w :: B) + N.c v w := by
      unfold cycleCost pathCost; rw [cycleArcs_cons, hcyc]; simp
    have hpv : pathCost N (Q v ++ [v]) = pathCost N (A ++ [w]) + pathCost N (w :: B) := by
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
    have e : pathCost N ((Q v ++ [v]) ++ [w]) = pathCost N (Q v ++ [v]) + N.c v w := by
      unfold pathCost; rw [pA_snoc2]; simp
    linarith

end CCca456

open CycleCanceling.MinMean in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsMinCost N f ↔ ¬ ∃ Γ : List V, IsResidualCycle N f Γ ∧ cycleCost N Γ < 0 := by
  constructor
  · rintro ⟨-, hmin⟩ ⟨Γ, hΓ, hneg⟩
    set L := cycleArcs Γ with hLdef
    have hLE : ∀ a ∈ L, a ∈ N.E := fun a ha => (hΓ.2.2 a ha).1
    obtain ⟨δ, hδ, hδL⟩ := CCca456.exists_delta L (fun a => resCap N f a.1 a.2)
      (fun a ha => (hΓ.2.2 a ha).2)
    have hlen : L.length = Γ.length := by
      rw [hLdef]; unfold cycleArcs; simp
    have hlpos : (0 : ℝ) < L.length := by
      rw [hlen]; exact_mod_cast List.length_pos_of_ne_nil hΓ.1
    set ε := δ / L.length with hε
    have hεpos : 0 < ε := div_pos hδ hlpos
    let g : V → V → ℝ := fun v w => f v w + ε * CCca456.dL L v w
    have hg : IsCirculation N g := by
      refine ⟨?_, ?_, ?_⟩
      · intro v w hvw
        show f v w + ε * CCca456.dL L v w ≤ N.u v w
        by_cases hm : (v, w) ∈ L
        · have h1 := hδL _ hm
          have h2 : ε * CCca456.dL L v w ≤ ε * L.length :=
            mul_le_mul_of_nonneg_left (CCca456.dL_le_length L v w) hεpos.le
          have h3 : ε * L.length = δ := by rw [hε]; field_simp
          simp only [resCap] at h1
          linarith
        · have := mul_nonpos_of_nonneg_of_nonpos hεpos.le (CCca456.dL_nonpos L v w hm)
          linarith [hf.1 v w hvw]
      · intro v w hvw
        show f v w + ε * CCca456.dL L v w = -(f w v + ε * CCca456.dL L w v)
        rw [hf.2.1 v w hvw, CCca456.dL_antisymm L v w]; ring
      · intro w
        show ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), (f v w + ε * CCca456.dL L v w) = 0
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, CCca456.dL_div N L hLE w, hf.2.2 w]
        rw [hLdef, CCca456.cycle_div]; ring
    have hc := hmin g hg
    have hcg : cost N g = cost N f + ε * cycleCost N Γ := by
      unfold cost
      show (1 / 2 : ℝ) * ∑ a ∈ N.E, N.c a.1 a.2 * (f a.1 a.2 + ε * CCca456.dL L a.1 a.2) = _
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have : ∑ a ∈ N.E, N.c a.1 a.2 * (ε * CCca456.dL L a.1 a.2) =
          ε * ∑ a ∈ N.E, N.c a.1 a.2 * CCca456.dL L a.1 a.2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_); ring
      rw [this, CCca456.dL_cost N L hLE]
      unfold cycleCost; rw [← hLdef]; ring
    have : ε * cycleCost N Γ < 0 := mul_neg_of_pos_of_neg hεpos hneg
    linarith
  · intro hneg
    refine ⟨hf, fun g hg => ?_⟩
    obtain ⟨p, hp⟩ := CCca456.exists_pot N f hneg
    let h : V → V → ℝ := fun v w => g v w - f v w
    have hanti : ∀ v w, (v, w) ∈ N.E → h v w = -h w v := by
      intro v w hvw; show g v w - f v w = -(g w v - f w v)
      rw [hg.2.1 v w hvw, hf.2.1 v w hvw]; ring
    have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), h v w = 0 := by
      intro w; show ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), (g v w - f v w) = 0
      rw [Finset.sum_sub_distrib, hg.2.2 w, hf.2.2 w]; ring
    have hz := CCca456.pot_zero N h p hanti hcons
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
