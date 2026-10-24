-- Prove2me | solution 1 for DirectedSearch.Approx.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:07:42.543656+00:00
-- url     : https://prove2.me/submissions/a097c4f3-9f62-4bdf-8721-f5828d5f607a

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Graphs

namespace DSA46

open DirectedSearch.Approx

variable {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- Indicator of the cross pair `{a, b}` at the entry `(m, w)`. -/
def ind (a b : M ⊕ W) (m : M) (w : W) : ℝ :=
  if (a = Sum.inl m ∧ b = Sum.inr w) ∨ (a = Sum.inr w ∧ b = Sum.inl m) then 1 else 0

/-- `+1` on `M`, `-1` on `W`. -/
def side : M ⊕ W → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

def isM (m : M) (z : M ⊕ W) : ℝ := if z = Sum.inl m then 1 else 0
def isW (w : W) (z : M ⊕ W) : ℝ := if z = Sum.inr w then 1 else 0

/-- Alternating signed edge vector of a walk. -/
def walkVec {G : SimpleGraph (M ⊕ W)} : {u v : M ⊕ W} → G.Walk u v → M → W → ℝ
  | _, _, .nil => fun _ _ => 0
  | u, _, .cons (v := x) _ p => fun m w => ind u x m w - walkVec p m w

lemma ind_row (u x : M ⊕ W) (h : side x = - side u) (m : M) :
    ∑ w, ind u x m w = isM m u + isM m x := by
  rcases u with a | b <;> rcases x with a' | b'
  · simp [side] at h; norm_num at h
  · simp [ind, isM, Finset.sum_ite_eq, ite_and, eq_comm]
  · simp [ind, isM, Finset.sum_ite_eq, ite_and, eq_comm]
  · simp [side] at h; norm_num at h

lemma ind_col (u x : M ⊕ W) (h : side x = - side u) (w : W) :
    ∑ m, ind u x m w = isW w u + isW w x := by
  rcases u with a | b <;> rcases x with a' | b'
  · simp [side] at h; norm_num at h
  · simp [ind, isW, Finset.sum_ite_eq, ite_and, eq_comm]
  · simp [ind, isW, Finset.sum_ite_eq, ite_and, eq_comm]
  · simp [side] at h; norm_num at h

lemma side_sq (u : M ⊕ W) : side u * side u = 1 := by
  rcases u with a | b <;> simp [side]

lemma walkVec_row {G : SimpleGraph (M ⊕ W)} (hG : ∀ a b, G.Adj a b → side b = - side a)
    {u v : M ⊕ W} (p : G.Walk u v) (m : M) :
    ∑ w, walkVec p m w = isM m u - side u * side v * isM m v := by
  induction p with
  | nil => simp [walkVec, side_sq]
  | @cons u x v h p ih =>
    simp only [walkVec]
    rw [Finset.sum_sub_distrib, ind_row u x (hG u x h) m, ih, hG u x h]
    ring

lemma walkVec_col {G : SimpleGraph (M ⊕ W)} (hG : ∀ a b, G.Adj a b → side b = - side a)
    {u v : M ⊕ W} (p : G.Walk u v) (w : W) :
    ∑ m, walkVec p m w = isW w u - side u * side v * isW w v := by
  induction p with
  | nil => simp [walkVec, side_sq]
  | @cons u x v h p ih =>
    simp only [walkVec]
    rw [Finset.sum_sub_distrib, ind_col u x (hG u x h) w, ih, hG u x h]
    ring

lemma walkVec_supp {G : SimpleGraph (M ⊕ W)} {u v : M ⊕ W} (p : G.Walk u v) (m : M) (w : W)
    (h : walkVec p m w ≠ 0) : G.Adj (Sum.inl m) (Sum.inr w) := by
  induction p with
  | nil => simp [walkVec] at h
  | @cons u x v hux p ih =>
    simp only [walkVec] at h
    by_cases hi : ind u x m w = 0
    · rw [hi, zero_sub, neg_ne_zero] at h
      exact ih h
    · unfold ind at hi
      split_ifs at hi with hc
      · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hux
        · exact hux.symm
      · exact absurd rfl hi

lemma supportGraph_adj' (β : M → W → ℝ) (x y : M ⊕ W) :
    (supportGraph β).Adj x y ↔ x ≠ y ∧
      ((∃ m w, x = Sum.inl m ∧ y = Sum.inr w ∧ 0 < β m w) ∨
        (∃ m w, y = Sum.inl m ∧ x = Sum.inr w ∧ 0 < β m w)) := by
  unfold supportGraph; rw [SimpleGraph.fromRel_adj]

lemma supportGraph_cross (β : M → W → ℝ) (m : M) (w : W) :
    (supportGraph β).Adj (Sum.inl m) (Sum.inr w) ↔ 0 < β m w := by
  rw [supportGraph_adj']; simp

lemma supportGraph_side (β : M → W → ℝ) (a b : M ⊕ W) (h : (supportGraph β).Adj a b) :
    side b = - side a := by
  rw [supportGraph_adj'] at h
  rcases h with ⟨_, ⟨m, w, rfl, rfl, _⟩ | ⟨m, w, rfl, rfl, _⟩⟩ <;> simp [side]

/-- A non-bridge cross edge gives a nonzero circulation supported on the support graph. -/
lemma circ_of_edge (β : M → W → ℝ) (m₀ : M) (w₀ : W)
    (hadj : (supportGraph β).Adj (Sum.inl m₀) (Sum.inr w₀))
    (hr : ((supportGraph β).deleteEdges {s(Sum.inl m₀, Sum.inr w₀)}).Reachable
      (Sum.inl m₀) (Sum.inr w₀)) :
    ∃ d : M → W → ℝ, (∀ m, ∑ w, d m w = 0) ∧ (∀ w, ∑ m, d m w = 0) ∧
      (∀ m w, d m w ≠ 0 → 0 < β m w) ∧ 0 < d m₀ w₀ := by
  obtain ⟨p⟩ := hr
  set G' := (supportGraph β).deleteEdges {s(Sum.inl m₀, Sum.inr w₀)} with hG'
  have hle : G' ≤ supportGraph β := SimpleGraph.deleteEdges_le _
  have hside : ∀ a b, G'.Adj a b → side b = - side a :=
    fun a b h => supportGraph_side β a b (hle h)
  refine ⟨fun m w => ind (Sum.inl m₀) (Sum.inr w₀) m w - walkVec p m w, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [Finset.sum_sub_distrib, ind_row _ _ (by simp [side]) m, walkVec_row hside p m]
    simp [isM, side]
  · intro w
    rw [Finset.sum_sub_distrib, ind_col _ _ (by simp [side]) w, walkVec_col hside p w]
    simp [isW, side]
    split_ifs <;> norm_num
  · intro m w h
    simp only at h
    by_cases hw : walkVec p m w = 0
    · rw [hw, sub_zero] at h
      by_cases hc : m₀ = m ∧ w₀ = w
      · obtain ⟨rfl, rfl⟩ := hc; exact (supportGraph_cross β _ _).mp hadj
      · exfalso; apply h; unfold ind; rw [if_neg]
        rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
        · exact hc ⟨Sum.inl_injective h1, Sum.inr_injective h2⟩
        · exact Sum.inl_ne_inr h1
    · exact (supportGraph_cross β m w).mp (hle (walkVec_supp p m w hw))
  · have h0 : walkVec p m₀ w₀ = 0 := by
      by_contra hne
      have := walkVec_supp p m₀ w₀ hne
      rw [hG', SimpleGraph.deleteEdges_adj] at this
      exact this.2 (Set.mem_singleton _)
    simp [h0, ind]

lemma circ_of_not_acyclic (β : M → W → ℝ) (hcyc : ¬ (supportGraph β).IsAcyclic) :
    ∃ d : M → W → ℝ, (∀ m, ∑ w, d m w = 0) ∧ (∀ w, ∑ m, d m w = 0) ∧
      (∀ m w, d m w ≠ 0 → 0 < β m w) ∧ ∃ m w, 0 < d m w := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hcyc
  push Not at hcyc
  obtain ⟨a, b, hab, hnb⟩ := hcyc
  rw [SimpleGraph.isBridge_iff, not_not] at hnb
  rcases a with m₀ | w₀ <;> rcases b with m₁ | w₁
  · exact absurd (supportGraph_side β _ _ hab) (by simp [side]; norm_num)
  · obtain ⟨d, h1, h2, h3, h4⟩ := circ_of_edge β m₀ w₁ hab hnb
    exact ⟨d, h1, h2, h3, m₀, w₁, h4⟩
  · rw [Sym2.eq_swap] at hnb
    obtain ⟨d, h1, h2, h3, h4⟩ := circ_of_edge β m₁ w₀ hab.symm hnb.symm
    exact ⟨d, h1, h2, h3, m₁, w₀, h4⟩
  · exact absurd (supportGraph_side β _ _ hab) (by simp [side]; norm_num)

section LP

variable (ρ : M → W → ℝ) (αM : M → ℝ) (αW : W → ℝ)

def Feas (β : M → W → ℝ) : Prop :=
  (∀ m w, 0 ≤ β m w) ∧ (∀ m, ∑ w, β m w ≤ αM m) ∧ (∀ w, ∑ m, β m w ≤ αW w)

def obj (β : M → W → ℝ) : ℝ := ∑ m, ∑ w, ρ m w * β m w

def Opt (β : M → W → ℝ) : Prop :=
  Feas αM αW β ∧ ∀ β', Feas αM αW β' → obj ρ β' ≤ obj ρ β

noncomputable def supp (β : M → W → ℝ) : ℕ :=
  (Finset.univ.filter (fun p : M × W => 0 < β p.1 p.2)).card

lemma obj_add (β d : M → W → ℝ) (t : ℝ) :
    obj ρ (fun m w => β m w + t * d m w) = obj ρ β + t * obj ρ d := by
  unfold obj
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring

lemma exists_opt (hαM : ∀ m, 0 ≤ αM m) (hαW : ∀ w, 0 ≤ αW w) : ∃ β, Opt ρ αM αW β := by
  set S : Set (M → W → ℝ) := {β | Feas αM αW β} with hS
  have hcl : IsClosed S := by
    have : S = (⋂ m, ⋂ w, {β : M → W → ℝ | 0 ≤ β m w}) ∩
        ((⋂ m, {β : M → W → ℝ | ∑ w, β m w ≤ αM m}) ∩
          (⋂ w, {β : M → W → ℝ | ∑ m, β m w ≤ αW w})) := by
      ext β; simp [hS, Feas]
    rw [this]
    refine (isClosed_iInter fun m => isClosed_iInter fun w => ?_).inter
      ((isClosed_iInter fun m => ?_).inter (isClosed_iInter fun w => ?_))
    · exact isClosed_le continuous_const ((continuous_apply w).comp (continuous_apply m))
    · exact isClosed_le (continuous_finset_sum _ fun w _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
    · exact isClosed_le (continuous_finset_sum _ fun m _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
  have hsub : S ⊆ Set.pi Set.univ (fun m => Set.pi Set.univ (fun _ : W => Set.Icc 0 (αM m))) := by
    intro β hβ m _ w _
    refine ⟨hβ.1 m w, ?_⟩
    calc β m w ≤ ∑ w', β m w' :=
          Finset.single_le_sum (fun w' _ => hβ.1 m w') (Finset.mem_univ w)
      _ ≤ αM m := hβ.2.1 m
  have hcpt : IsCompact S :=
    (isCompact_univ_pi fun m => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hcl hsub
  have hne : S.Nonempty := ⟨0, fun m w => le_rfl, fun m => by simp [hαM m],
    fun w => by simp [hαW w]⟩
  have hcont : Continuous (obj ρ) := by
    unfold obj
    exact continuous_finset_sum _ fun m _ => continuous_finset_sum _
      fun w _ => continuous_const.mul ((continuous_apply w).comp (continuous_apply m))
  obtain ⟨β, hβ, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
  exact ⟨β, hβ, fun β' hβ' => hmax hβ'⟩

lemma perturb (β : M → W → ℝ) (hopt : Opt ρ αM αW β) (d : M → W → ℝ)
    (hrow : ∀ m, ∑ w, d m w = 0) (hcol : ∀ w, ∑ m, d m w = 0)
    (hsupp : ∀ m w, d m w ≠ 0 → 0 < β m w) (m₀ : M) (w₀ : W) (hpos : 0 < d m₀ w₀) :
    ∃ γ, Opt ρ αM αW γ ∧ supp γ < supp β := by
  obtain ⟨⟨hβ0, hβr, hβc⟩, hβmax⟩ := hopt
  -- a negative entry in row m₀
  have hneg : ∃ w, d m₀ w < 0 := by
    by_contra hn; push Not at hn
    have : 0 < ∑ w, d m₀ w :=
      Finset.sum_pos' (fun w _ => hn w) ⟨w₀, Finset.mem_univ _, hpos⟩
    linarith [hrow m₀]
  obtain ⟨w₁, hw₁⟩ := hneg
  set Sp := Finset.univ.filter (fun p : M × W => 0 < d p.1 p.2) with hSp
  set Sn := Finset.univ.filter (fun p : M × W => d p.1 p.2 < 0) with hSn
  have hSpne : Sp.Nonempty := ⟨(m₀, w₀), by simp [hSp, hpos]⟩
  have hSnne : Sn.Nonempty := ⟨(m₀, w₁), by simp [hSn, hw₁]⟩
  obtain ⟨pp, hpp, hppmin⟩ := Sp.exists_min_image (fun p => β p.1 p.2 / d p.1 p.2) hSpne
  obtain ⟨pn, hpn, hpnmin⟩ := Sn.exists_min_image (fun p => β p.1 p.2 / (- d p.1 p.2)) hSnne
  simp only [hSp, hSn, Finset.mem_filter, Finset.mem_univ, true_and] at hpp hpn hppmin hpnmin
  set tp := β pp.1 pp.2 / d pp.1 pp.2 with htp
  set tn := β pn.1 pn.2 / (- d pn.1 pn.2) with htn
  have htp0 : 0 < tp := div_pos (hsupp _ _ hpp.ne') hpp
  have htn0 : 0 < tn := div_pos (hsupp _ _ hpn.ne) (by linarith)
  set γ1 : M → W → ℝ := fun m w => β m w + (-tp) * d m w with hγ1
  set γ2 : M → W → ℝ := fun m w => β m w + tn * d m w with hγ2
  have hrows : ∀ (t : ℝ) m, ∑ w, (β m w + t * d m w) = ∑ w, β m w := by
    intro t m; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow m, mul_zero, add_zero]
  have hcols : ∀ (t : ℝ) w, ∑ m, (β m w + t * d m w) = ∑ m, β m w := by
    intro t w; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol w, mul_zero, add_zero]
  have hγ1nn : ∀ m w, 0 ≤ γ1 m w := by
    intro m w
    simp only [hγ1]
    rcases lt_or_ge 0 (d m w) with hd | hd
    · have := hppmin (m, w) hd
      simp only at this
      rw [le_div_iff₀ hd] at this
      linarith
    · nlinarith [hβ0 m w]
  have hγ2nn : ∀ m w, 0 ≤ γ2 m w := by
    intro m w
    simp only [hγ2]
    rcases lt_or_ge (d m w) 0 with hd | hd
    · have := hpnmin (m, w) hd
      simp only at this
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · nlinarith [hβ0 m w]
  have hF1 : Feas αM αW γ1 :=
    ⟨hγ1nn, fun m => by simp only [hγ1]; rw [hrows]; exact hβr m,
      fun w => by simp only [hγ1]; rw [hcols]; exact hβc w⟩
  have hF2 : Feas αM αW γ2 :=
    ⟨hγ2nn, fun m => by simp only [hγ2]; rw [hrows]; exact hβr m,
      fun w => by simp only [hγ2]; rw [hcols]; exact hβc w⟩
  have e1 := hβmax γ1 hF1
  have e2 := hβmax γ2 hF2
  rw [hγ1, obj_add] at e1
  rw [hγ2, obj_add] at e2
  have hd0 : obj ρ d = 0 := by
    rcases lt_trichotomy (obj ρ d) 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  refine ⟨γ1, ⟨hF1, fun β' hβ' => ?_⟩, ?_⟩
  · rw [hγ1, obj_add, hd0, mul_zero, add_zero]; exact hβmax β' hβ'
  · unfold supp
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨pp, ?_, ?_⟩
      · simp [hsupp _ _ hpp.ne']
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hγ1, not_lt]
        rw [htp]; field_simp; linarith
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hγ1] at hp ⊢
      by_cases hd : d p.1 p.2 = 0
      · rw [hd, mul_zero, add_zero] at hp; exact hp
      · exact hsupp _ _ hd

end LP

end DSA46

open DirectedSearch.Approx DSA46 in
theorem solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (ρ : M → W → ℝ) (αM : M → ℝ) (αW : W → ℝ) (hαM : ∀ m, 0 ≤ αM m) (hαW : ∀ w, 0 ≤ αW w) :
    ∃ βstar : M → W → ℝ,
      ((∀ m w, 0 ≤ βstar m w) ∧ (∀ m, ∑ w, βstar m w ≤ αM m) ∧ (∀ w, ∑ m, βstar m w ≤ αW w)) ∧
      (∀ β : M → W → ℝ, (∀ m w, 0 ≤ β m w) → (∀ m, ∑ w, β m w ≤ αM m) →
        (∀ w, ∑ m, β m w ≤ αW w) → ∑ m, ∑ w, ρ m w * β m w ≤ ∑ m, ∑ w, ρ m w * βstar m w) ∧
      (supportGraph βstar).IsAcyclic := by
  classical
  obtain ⟨β1, hβ1⟩ := exists_opt ρ αM αW hαM hαW
  have hex : ∃ k, ∃ β, Opt ρ αM αW β ∧ supp β = k := ⟨_, β1, hβ1, rfl⟩
  obtain ⟨β, hβ, hk⟩ := Nat.find_spec hex
  refine ⟨β, hβ.1, fun β' h1 h2 h3 => hβ.2 β' ⟨h1, h2, h3⟩, ?_⟩
  by_contra hcyc
  obtain ⟨d, hrow, hcol, hsupp, m₀, w₀, hpos⟩ := circ_of_not_acyclic β hcyc
  obtain ⟨γ, hγ, hlt⟩ := perturb ρ αM αW β hβ d hrow hcol hsupp m₀ w₀ hpos
  exact Nat.find_min hex (hk ▸ hlt) ⟨γ, hγ, rfl⟩
