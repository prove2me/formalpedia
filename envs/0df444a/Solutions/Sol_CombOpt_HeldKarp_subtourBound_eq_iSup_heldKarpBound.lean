-- Prove2me | solution 1 for CombOpt.HeldKarp.subtourBound_eq_iSup_heldKarpBound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:45:32.476766+00:00
-- url     : https://prove2.me/submissions/6d89b318-6cbe-478e-baca-2f9cab2792dd

import Mathlib
import Theorems.Thm_CombOpt_HeldKarp_minOneTreeCost_eq_oneTreeLPValue
import Theorems.Thm_CombOpt_HeldKarp_subtourFeasible_iff_insideFeasible
import Theorems.Thm_CombOpt_HeldKarp_farkas_lemma_inequalities
import Definitions.Def_CombOpt_HeldKarp_Graph_subtourBound
import Definitions.Def_CombOpt_HeldKarp_Graph_heldKarpBound
import Definitions.Def_CombOpt_HeldKarp_Graph_minOneTreeCost
import Definitions.Def_CombOpt_HeldKarp_Graph_oneTreeLPValue
import Definitions.Def_CombOpt_HeldKarp_Graph_InsideFeasible

set_option autoImplicit false

namespace HK76

open CombOpt.HeldKarp

section
variable {V E : Type*} [Fintype V] [Fintype E]

lemma lift_eq_sum [DecidableEq V] (y : V → ℝ) (z : Sym2 V) (hz : ¬ z.IsDiag) :
    Sym2.lift ⟨fun u v => y u + y v, fun u v => add_comm (y u) (y v)⟩ z
      = ∑ v, if v ∈ z then y v else 0 := by
  induction z using Sym2.ind with
  | h u w =>
    have huw : u ≠ w := by simpa using hz
    rw [Sym2.lift_mk, ← Finset.sum_filter]
    have : (Finset.univ.filter (fun v => v ∈ s(u, w))) = {u, w} := by
      ext v; simp [Sym2.mem_iff]
    rw [this, Finset.sum_pair huw]

lemma mem_cut_single (G : CombOpt.HeldKarp.Graph V E) (hG : ∀ e, ¬ (G.ends e).IsDiag) (v : V) (e : E) :
    e ∈ G.cut {v} ↔ v ∈ G.ends e := by
  classical
  unfold CombOpt.HeldKarp.Graph.cut
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, _⟩; exact ha
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, Sym2.Mem.other hv, Sym2.other_mem hv, fun h => hG e ?_⟩
    have := Sym2.other_spec hv
    rw [h] at this
    rw [← this]; simp

lemma cut_sum [DecidableEq V] (G : CombOpt.HeldKarp.Graph V E) (hG : ∀ e, ¬ (G.ends e).IsDiag) (v : V) (x : E → ℝ) :
    ∑ e ∈ G.cut {v}, x e = ∑ e, if v ∈ G.ends e then x e else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e; simp [mem_cut_single G hG]

lemma lift_mul_sum [DecidableEq V] (G : CombOpt.HeldKarp.Graph V E) (hG : ∀ e, ¬ (G.ends e).IsDiag) (y : V → ℝ) (x : E → ℝ) :
    ∑ e, Sym2.lift ⟨fun u v => y u + y v, fun u v => add_comm (y u) (y v)⟩ (G.ends e) * x e
      = ∑ v, y v * ∑ e, (if v ∈ G.ends e then x e else 0) := by
  simp_rw [lift_eq_sum y _ (hG _), Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun e _ => ?_))
  split_ifs <;> ring

lemma sum_in_eq [DecidableEq E] (s : Finset E) (x : E → ℝ) :
    ∑ e ∈ s, x e = ∑ e, (if e ∈ s then (1:ℝ) else 0) * x e := by
  simp [ite_mul, Finset.sum_ite_mem]

lemma einf_cases {α : Type*} [Fintype α] (P : α → Prop) (f : α → ℝ) :
    (⨅ a, ⨅ (_ : P a), (f a : EReal)) = ⊤ ∨
      ∃ a, P a ∧ (⨅ a, ⨅ (_ : P a), (f a : EReal)) = f a := by
  classical
  by_cases h : ∃ a, P a
  · right
    obtain ⟨a, ha, hmin⟩ := (Finset.univ.filter P).exists_min_image f
      (by obtain ⟨a, ha⟩ := h; exact ⟨a, by simp [ha]⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmin
    exact ⟨a, ha, le_antisymm (iInf₂_le a ha)
      (le_iInf₂ fun b hb => EReal.coe_le_coe_iff.mpr (hmin b hb))⟩
  · left
    push_neg at h
    simp [h]

lemma le_inf_add_inf {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) (f : α → ℝ)
    (Q : β → Prop) (g : β → ℝ) (r : ℝ) (h : ∀ a, P a → ∀ b, Q b → r ≤ f a + g b) :
    (r : EReal) ≤ (⨅ a, ⨅ (_ : P a), (f a : EReal)) + ⨅ b, ⨅ (_ : Q b), (g b : EReal) := by
  rcases einf_cases P f with hA | ⟨a, ha, hA⟩ <;> rcases einf_cases Q g with hB | ⟨b, hb, hB⟩ <;>
    rw [hA, hB]
  · simp
  · rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]; exact le_top
  · rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]; exact le_top
  · rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (h a ha b hb)

/-- edges of `δ(v₁)` are not in a spanning tree of `G \ v₁`. -/
lemma sum_oneTree (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) [DecidableEq E] (e f : E) (T : Finset E)
    (hef : e ≠ f) (he : e ∈ G.cut {v₁}) (hf : f ∈ G.cut {v₁}) (hT : G.IsSpanningTreeDelete v₁ T)
    (w : E → ℝ) : ∑ g ∈ insert e (insert f T), w g = w e + w f + ∑ g ∈ T, w g := by
  classical
  have hv : ∀ g ∈ G.cut {v₁}, v₁ ∈ G.ends g := by
    intro g hg
    unfold CombOpt.HeldKarp.Graph.cut at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hg
    obtain ⟨⟨a, ha, rfl⟩, _⟩ := hg; exact ha
  have heT : e ∉ T := fun h => hT.1 e h (hv e he)
  have hfT : f ∉ T := fun h => hT.1 f h (hv f hf)
  rw [Finset.sum_insert (by simp [hef, heT]), Finset.sum_insert hfT]; ring

lemma oneTreeBound_le (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) [DecidableEq E] (c : E → ℝ) :
    G.oneTreeBound c v₁ ≤ G.minOneTreeCost c v₁ := by
  unfold CombOpt.HeldKarp.Graph.minOneTreeCost
  refine le_iInf₂ fun J hJ => ?_
  obtain ⟨e, f, T, hef, he, hf, hT, rfl⟩ := hJ
  rw [sum_oneTree G v₁ e f T hef he hf hT c]
  calc G.oneTreeBound c v₁
      ≤ ((c e + c f : ℝ) : EReal) + ((∑ g ∈ T, c g : ℝ) : EReal) := by
        unfold CombOpt.HeldKarp.Graph.oneTreeBound
        exact add_le_add (iInf₂_le (e, f) ⟨hef, he, hf⟩) (iInf₂_le T hT)
    _ = ((c e + c f + ∑ g ∈ T, c g : ℝ) : EReal) := by norm_cast

/-- valid (pair, tree) triples describing the 1-trees. -/
def Trip (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) : Type _ :=
  {q : (E × E) × Finset E // q.1.1 ≠ q.1.2 ∧ q.1.1 ∈ G.cut {v₁} ∧ q.1.2 ∈ G.cut {v₁} ∧
    G.IsSpanningTreeDelete v₁ q.2}

noncomputable def tripFintype (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) : Fintype (Trip G v₁) := by
  classical
  unfold Trip; infer_instance

def JJ [DecidableEq E] {G : CombOpt.HeldKarp.Graph V E} {v₁ : V} (q : Trip G v₁) : Finset E :=
  insert q.1.1.1 (insert q.1.1.2 q.1.2)

/-- transfer of a valid inequality of the 1-tree LP to every 1-tree, using (7.7). -/
lemma transfer (G : CombOpt.HeldKarp.Graph V E) (v₁ : V) [DecidableEq V] [DecidableEq E]
    (hA : ∀ c : E → ℝ, G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁)
    (w : E → ℝ) (β : ℝ) (hw : ∀ x, G.OneTreeLPFeasible v₁ x → ∑ e, w e * x e ≤ β)
    (J : Finset E) (hJ : G.IsOneTree v₁ J) : ∑ e ∈ J, w e ≤ β := by
  have h1 : G.minOneTreeCost (-w) v₁ ≤ ((∑ e ∈ J, (-w) e : ℝ) : EReal) := iInf₂_le J hJ
  have h2 : ((-β : ℝ) : EReal) ≤ G.oneTreeLPValue (-w) v₁ := by
    refine le_iInf₂ fun x hx => EReal.coe_le_coe_iff.mpr ?_
    have := hw x hx
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    linarith
  rw [hA] at h1
  have := EReal.coe_le_coe_iff.mp (h2.trans h1)
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at this
  linarith

end

theorem core {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : CombOpt.HeldKarp.Graph V E) (hG : ∀ e : E, ¬ (G.ends e).IsDiag) (c : E → ℝ) (v₁ : V)
    [Fintype (Trip G v₁)]
    (hA : ∀ c : E → ℝ, G.minOneTreeCost c v₁ = G.oneTreeLPValue c v₁)
    (hB : ∀ x : E → ℝ, G.SubtourFeasible x ↔ G.InsideFeasible v₁ x)
    (hF : ∀ (a : Trip G v₁ → V → ℝ) (b : Trip G v₁ → ℝ),
      (∃ y : V → ℝ, ∀ i, ∑ s, a i s * y s ≤ b i) ↔
        ∀ l : Trip G v₁ → ℝ, (∀ i, 0 ≤ l i) → (∀ s, ∑ i, l i * a i s = 0) → 0 ≤ ∑ i, l i * b i) :
    G.subtourBound c = ⨆ y : V → ℝ, G.heldKarpBound c v₁ y ∧
      (G.subtourBound c ≠ ⊤ → ∃ y : V → ℝ, G.heldKarpBound c v₁ y = G.subtourBound c) := by
  have hOT : ∀ x, G.SubtourFeasible x → G.OneTreeLPFeasible v₁ x := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := (hB x).1 hx
    exact ⟨h2, h3, h4, h1 v₁⟩
  -- weak duality
  have hW : ∀ y, G.heldKarpBound c v₁ y ≤ G.subtourBound c := by
    intro y
    unfold CombOpt.HeldKarp.Graph.subtourBound
    refine le_iInf₂ fun x hx => ?_
    have hdeg : ∀ v, ∑ e ∈ G.cut {v}, x e = 2 := ((hB x).1 hx).1
    have hsplit : ∑ e, c e * x e = ∑ e, G.reducedCost c y e * x e + 2 * ∑ v, y v := by
      have := lift_mul_sum G hG y x
      simp_rw [← cut_sum G hG, hdeg] at this
      unfold CombOpt.HeldKarp.Graph.reducedCost
      simp only [sub_mul, Finset.sum_sub_distrib, this, ← Finset.sum_mul]
      ring
    have h1 : G.oneTreeBound (G.reducedCost c y) v₁
        ≤ ((∑ e, G.reducedCost c y e * x e : ℝ) : EReal) :=
      (oneTreeBound_le G v₁ _).trans ((hA _).le.trans (iInf₂_le x (hOT x hx)))
    unfold CombOpt.HeldKarp.Graph.heldKarpBound
    calc ((2 * ∑ v, y v : ℝ) : EReal) + G.oneTreeBound (G.reducedCost c y) v₁
        ≤ ((2 * ∑ v, y v : ℝ) : EReal) + ((∑ e, G.reducedCost c y e * x e : ℝ) : EReal) :=
          add_le_add le_rfl h1
      _ = ((∑ e, c e * x e : ℝ) : EReal) := by
          rw [hsplit, ← EReal.coe_add]; congr 1; ring
  have hbot : ((-∑ e, |c e| : ℝ) : EReal) ≤ G.subtourBound c := by
    unfold CombOpt.HeldKarp.Graph.subtourBound
    refine le_iInf₂ fun x hx => EReal.coe_le_coe_iff.mpr ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    obtain ⟨h0, h1⟩ := hx.2.2 e
    rcases le_or_gt 0 (c e) with h | h
    · have := abs_nonneg (c e); nlinarith
    · rw [abs_of_neg h]; nlinarith
  -- strong duality via Farkas
  have hK : ∀ t : ℝ, (t : EReal) ≤ G.subtourBound c →
      ∃ y, (t : EReal) ≤ G.heldKarpBound c v₁ y := by
    intro t ht
    let χ : Trip G v₁ → E → ℝ := fun q e => if e ∈ JJ q then 1 else 0
    let dg : Trip G v₁ → V → ℝ := fun q v => ∑ e, if v ∈ G.ends e then χ q e else 0
    have hJ1 : ∀ q : Trip G v₁, G.IsOneTree v₁ (JJ q) := fun q =>
      ⟨q.1.1.1, q.1.1.2, q.1.2, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, rfl⟩
    have hχ : ∀ q (w : E → ℝ), ∑ e ∈ JJ q, w e = ∑ e, w e * χ q e := by
      intro q w; rw [sum_in_eq]; exact Finset.sum_congr rfl (fun e _ => mul_comm _ _)
    have hite : ∀ (v : V) (z : E → ℝ), (∑ e, if v ∈ G.ends e then z e else 0)
        = ∑ e, (if v ∈ G.ends e then (1:ℝ) else 0) * z e :=
      fun v z => Finset.sum_congr rfl (fun e _ => by split_ifs <;> simp)
    rcases em (∃ y : V → ℝ, ∀ q, ∑ v, (dg q v - 2) * y v ≤ (∑ e ∈ JJ q, c e) - t)
      with ⟨y, hy⟩ | hno
    · refine ⟨y, ?_⟩
      have hq : ∀ q : Trip G v₁, t - 2 * ∑ v, y v ≤ ∑ e ∈ JJ q, G.reducedCost c y e := by
        intro q
        have h1 := hy q
        have h2 : ∑ e ∈ JJ q, G.reducedCost c y e = ∑ e ∈ JJ q, c e - ∑ v, y v * dg q v := by
          unfold CombOpt.HeldKarp.Graph.reducedCost
          rw [Finset.sum_sub_distrib, hχ q (fun e => Sym2.lift
            ⟨fun u v => y u + y v, fun u v => add_comm (y u) (y v)⟩ (G.ends e)),
            lift_mul_sum G hG y (χ q)]
        rw [h2]
        have h3 : ∑ v, (dg q v - 2) * y v = ∑ v, y v * dg q v - 2 * ∑ v, y v := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun v _ => by ring)
        linarith
      have hle : ((t - 2 * ∑ v, y v : ℝ) : EReal) ≤ G.oneTreeBound (G.reducedCost c y) v₁ := by
        unfold CombOpt.HeldKarp.Graph.oneTreeBound
        refine le_inf_add_inf _ _ _ _ _ (fun p hp T hT => ?_)
        have := hq ⟨(p, T), hp.1, hp.2.1, hp.2.2, hT⟩
        dsimp only [JJ] at this
        rwa [sum_oneTree G v₁ p.1 p.2 T hp.1 hp.2.1 hp.2.2 hT] at this
      unfold CombOpt.HeldKarp.Graph.heldKarpBound
      calc (t : EReal) = ((2 * ∑ v, y v : ℝ) : EReal) + ((t - 2 * ∑ v, y v : ℝ) : EReal) := by
            rw [← EReal.coe_add]; congr 1; ring
        _ ≤ _ := add_le_add le_rfl hle
    · exfalso
      have hl := (not_congr (hF (fun q v => dg q v - 2) (fun q => ∑ e ∈ JJ q, c e - t))).1 hno
      push_neg at hl
      obtain ⟨l, hl0, hlA, hlb⟩ := hl
      have hLpos : 0 < ∑ q, l q := by
        rcases (Finset.sum_nonneg (fun q _ => hl0 q)).lt_or_eq with h | h
        · exact h
        · exfalso
          have hz : ∀ q, l q = 0 := fun q =>
            (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hl0 q)).1 h.symm q (Finset.mem_univ q)
          simp [hz] at hlb
      let lam : Trip G v₁ → ℝ := fun q => l q / ∑ q, l q
      let x : E → ℝ := fun e => ∑ q, lam q * χ q e
      have hlam0 : ∀ q, 0 ≤ lam q := fun q => div_nonneg (hl0 q) hLpos.le
      have hlam1 : ∑ q, lam q = 1 := by
        simp only [lam, ← Finset.sum_div]; exact div_self hLpos.ne'
      have hx : ∀ w : E → ℝ, ∑ e, w e * x e = ∑ q, lam q * ∑ e ∈ JJ q, w e := by
        intro w
        calc ∑ e, w e * x e = ∑ e, ∑ q, lam q * (w e * χ q e) := by
              refine Finset.sum_congr rfl (fun e _ => ?_)
              simp only [x, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun q _ => by ring)
          _ = ∑ q, ∑ e, lam q * (w e * χ q e) := Finset.sum_comm
          _ = ∑ q, lam q * ∑ e ∈ JJ q, w e := by
              refine Finset.sum_congr rfl (fun q _ => ?_)
              rw [hχ q w, Finset.mul_sum]
      have hxle : ∀ (w : E → ℝ) (β : ℝ),
          (∀ x', G.OneTreeLPFeasible v₁ x' → ∑ e, w e * x' e ≤ β) → ∑ e, w e * x e ≤ β := by
        intro w β hw
        rw [hx w]
        calc ∑ q, lam q * ∑ e ∈ JJ q, w e ≤ ∑ q, lam q * β :=
              Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
                (transfer G v₁ hA w β hw _ (hJ1 q)) (hlam0 q))
          _ = β := by rw [← Finset.sum_mul, hlam1, one_mul]
      have hset_le : ∀ (s : Finset E) (β : ℝ),
          (∀ x', G.OneTreeLPFeasible v₁ x' → ∑ e ∈ s, x' e ≤ β) → ∑ e ∈ s, x e ≤ β := by
        intro s β h
        have key : ∀ z : E → ℝ, ∑ e, (if e ∈ s then (1:ℝ) else 0) * z e = ∑ e ∈ s, z e :=
          fun z => (sum_in_eq s z).symm
        have := hxle (fun e => if e ∈ s then (1:ℝ) else 0) β
          (fun x' hx' => (key x').le.trans (h x' hx'))
        exact (key x).symm.le.trans this
      have hset_ge : ∀ (s : Finset E) (β : ℝ),
          (∀ x', G.OneTreeLPFeasible v₁ x' → β ≤ ∑ e ∈ s, x' e) → β ≤ ∑ e ∈ s, x e := by
        intro s β h
        have key : ∀ z : E → ℝ, ∑ e, -(if e ∈ s then (1:ℝ) else 0) * z e = -∑ e ∈ s, z e := by
          intro z
          rw [sum_in_eq s z, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun e _ => by ring)
        have := hxle (fun e => -(if e ∈ s then (1:ℝ) else 0)) (-β)
          (fun x' hx' => (key x').le.trans (by linarith [h x' hx']))
        have h2 := (key x).symm.le.trans this
        linarith
      have hdeg : ∀ v, ∑ e ∈ G.cut {v}, x e = 2 := by
        intro v
        have hd : ∀ q, dg q v = ∑ e ∈ JJ q, (if v ∈ G.ends e then (1:ℝ) else 0) := fun q => by
          rw [hχ q]; exact hite v (χ q)
        have h2 := hlA v
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h2
        rw [cut_sum G hG, hite v x, hx]
        simp only [← hd, lam, div_mul_eq_mul_div, ← Finset.sum_div]
        rw [div_eq_iff hLpos.ne']
        linarith
      have hxF : G.SubtourFeasible x := by
        refine (hB x).2 ⟨hdeg, fun S hS hv => hset_le _ _ (fun x' hx' => hx'.1 S hS hv),
          le_antisymm (hset_le _ _ (fun x' hx' => hx'.2.1.le))
            (hset_ge _ _ (fun x' hx' => hx'.2.1.ge)), fun e => ⟨?_, ?_⟩⟩
        · exact Finset.sum_nonneg (fun q _ => mul_nonneg (hlam0 q) (by
            simp only [χ]; split_ifs <;> norm_num))
        · calc x e ≤ ∑ q, lam q := Finset.sum_le_sum (fun q _ => mul_le_of_le_one_right (hlam0 q)
                (by simp only [χ]; split_ifs <;> norm_num))
            _ = 1 := hlam1
      have hcost : ∑ e, c e * x e < t := by
        rw [hx c]
        have h2 := hlb
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h2
        simp only [lam, div_mul_eq_mul_div, ← Finset.sum_div]
        rw [div_lt_iff₀ hLpos]
        linarith
      have hle : G.subtourBound c ≤ ((∑ e, c e * x e : ℝ) : EReal) := iInf₂_le x hxF
      exact absurd (EReal.coe_le_coe_iff.mp (ht.trans hle)) (not_le.mpr hcost)
  have hSbot : G.subtourBound c ≠ ⊥ := fun h => by
    rw [h] at hbot; exact EReal.coe_ne_bot _ (le_bot_iff.mp hbot)
  by_cases hS : G.subtourBound c = ⊤
  · refine ⟨?_, fun h => absurd hS h⟩
    rw [hS, eq_comm, EReal.eq_top_iff_forall_lt]
    intro r
    obtain ⟨y, hy⟩ := hK (r + 1) (by rw [hS]; exact le_top)
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith))
      (hy.trans (le_iSup (fun y => G.heldKarpBound c v₁ y) y))
  · have hs : (((G.subtourBound c).toReal : ℝ) : EReal) = G.subtourBound c :=
      EReal.coe_toReal hS hSbot
    obtain ⟨y, hy⟩ := hK _ hs.le
    have hyS : G.heldKarpBound c v₁ y = G.subtourBound c := le_antisymm (hW y) (hs.ge.trans hy)
    exact ⟨le_antisymm (hyS.symm.le.trans (le_iSup (fun y => G.heldKarpBound c v₁ y) y))
      (iSup_le hW), fun _ => ⟨y, hyS⟩⟩

end HK76

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    (G : CombOpt.HeldKarp.Graph V E) (hG : ∀ e : E, ¬ (G.ends e).IsDiag) (c : E → ℝ) (v₁ : V) :
    G.subtourBound c = ⨆ y : V → ℝ, G.heldKarpBound c v₁ y ∧
      (G.subtourBound c ≠ ⊤ → ∃ y : V → ℝ, G.heldKarpBound c v₁ y = G.subtourBound c) := by
  classical
  letI := HK76.tripFintype G v₁
  exact HK76.core G hG c v₁
    (fun c => CombOpt.HeldKarp.minOneTreeCost_eq_oneTreeLPValue G v₁
      (fun e h => hG e (by rw [h]; simp)) c)
    (fun x => CombOpt.HeldKarp.subtourFeasible_iff_insideFeasible G v₁
      (fun e u h => (hG e (by rw [h]; simp)).elim) x)
    (fun a b => CombOpt.HeldKarp.farkas_lemma_inequalities a b)
