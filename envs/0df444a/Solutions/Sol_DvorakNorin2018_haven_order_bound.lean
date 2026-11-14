-- Prove2me | solution 1 for DvorakNorin2018.haven_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T18:26:33.519764+00:00
-- url     : https://prove2.me/submissions/9e8f27c1-9c1d-4f60-814b-d6c967e6f351

import Theorems.Thm_DvorakNorin2018_haven_cloud_balanced_configuration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.CloudCut
open TreewidthApprox.Pushed

noncomputable def crossFlow {V : Type} [Fintype V]
    (flow : V → V → ℝ) (A B : Finset V) : ℝ := ∑ x ∈ A, ∑ y ∈ B, flow x y

lemma conservation_cut {V : Type} [Fintype V] [DecidableEq V]
    (supply : V → ℝ) (flow : V → V → ℝ) (R : Finset V)
    (hcons : ∀ v ∈ R, supply v + ∑ u, flow u v = ∑ u, flow v u) :
    (∑ v ∈ R, supply v) + crossFlow flow Rᶜ R = crossFlow flow R Rᶜ := by
  have heq := Finset.sum_congr rfl hcons
  rw [Finset.sum_add_distrib] at heq
  have hout : (∑ v ∈ R, ∑ u, flow v u) = crossFlow flow R R + crossFlow flow R Rᶜ := by
    unfold crossFlow
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => (Finset.sum_add_sum_compl R (fun u => flow v u)).symm)
  have hin : (∑ v ∈ R, ∑ u, flow u v) = crossFlow flow R R + crossFlow flow Rᶜ R := by
    rw [Finset.sum_comm]
    unfold crossFlow
    exact (Finset.sum_add_sum_compl R (fun u => ∑ v ∈ R, flow u v)).symm
  rw [hout, hin] at heq
  linarith

/-- The supply outside a vertex cut must flow into the cut or across its boundary. -/
theorem supply_le_outgoing {V : Type} [Fintype V] [DecidableEq V]
    (supply : V → ℝ) (flow : V → V → ℝ) (R : Finset V)
    (hnonneg : ∀ x y, 0 ≤ flow x y)
    (hcons : ∀ v ∈ R, supply v + ∑ u, flow u v = ∑ u, flow v u) :
    (∑ v ∈ R, supply v) ≤ crossFlow flow R Rᶜ := by
  have h := conservation_cut supply flow R hcons
  have hn : 0 ≤ crossFlow flow Rᶜ R :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hnonneg x y))
  linarith


end StableMSR.Recovery.CloudCut
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.CloudCounting
open TameCloud Havens TreewidthApprox.Pushed

lemma supply_le_boundary_congestion {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V}
    (hp : Cloud G W α p) (Q D : Finset V) (hDQ : D ⊆ Q)
    (hW : ∀ v ∈ Q \ D, v ∉ W)
    (hout : ∀ v ∈ Q \ D, ∀ u ∉ Q, p.2 (v,u) = 0) :
    (∑ v ∈ Q, p.1 v) ≤ α * D.card := by
  classical
  let I := Q \ D
  have hI := CloudCut.supply_le_outgoing p.1 (fun u v => p.2 (u,v)) I
    (fun u v => hp.flow (u,v)) (fun v hv => hp.conserve v (hW v hv))
  have hDI : D ⊆ Iᶜ := by
    intro v hv; exact Finset.mem_compl.mpr (fun hi => (Finset.mem_sdiff.mp hi).2 hv)
  have hc : CloudCut.crossFlow (fun u v => p.2 (u,v)) I Iᶜ =
      CloudCut.crossFlow (fun u v => p.2 (u,v)) I D := by
    unfold CloudCut.crossFlow
    apply Finset.sum_congr rfl
    intro v hv
    apply (Finset.sum_subset hDI ?_).symm
    intro u hu huD
    exact hout v hv u (fun huQ => (Finset.mem_compl.mp hu) (Finset.mem_sdiff.mpr ⟨huQ,huD⟩))
  have hle : CloudCut.crossFlow (fun u v => p.2 (u,v)) I D ≤ ∑ v ∈ D, incoming p v := by
    unfold CloudCut.crossFlow incoming
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun v _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun u _ _ => hp.flow (u,v)))
  have hb : (∑ v ∈ D, p.1 v) + (∑ v ∈ D, incoming p v) ≤ α * D.card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _v ∈ D, α := Finset.sum_le_sum (fun v _ => hp.bound v)
      _ = _ := by simp [mul_comm]
  have he : (∑ v ∈ Q, p.1 v) = (∑ v ∈ I, p.1 v) + (∑ v ∈ D, p.1 v) := by
    rw [← Finset.sdiff_union_of_subset hDQ, Finset.sum_union Finset.sdiff_disjoint]
  rw [hc] at hI
  linarith

lemma positive_flow_target_saturated {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V}
    (hp : Cloud G W α p) (ht : Tame W α p) {u v : V} (hpos : 0 < p.2 (u,v)) :
    p.1 v = 1 := by
  by_contra hn
  have hlt : p.1 v < 1 := lt_of_le_of_ne (hp.supply v).2 hn
  have hi : p.2 (u,v) ≤ incoming p v := Finset.single_le_sum
    (fun x _ => hp.flow (x,v)) (Finset.mem_univ u)
  have hc : 0 < congestion p v := by
    dsimp [congestion]; have := (hp.supply v).1; linarith
  have hz := ht.1 v ⟨hlt,Or.inl hc⟩ u
  linarith

lemma hungry_has_positive_successor {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V}
    (hp : Cloud G W α p) {v : V} (hv : Hungry W p v) (hw : v ∉ W) :
    ∃ u, 0 < p.2 (v,u) := by
  have hc : 0 < congestion p v := hv.2.resolve_right hw
  rw [hp.conserve v hw] at hc
  obtain ⟨u,_,hu⟩ := (Finset.sum_pos_iff_of_nonneg (fun u _ => hp.flow (v,u))).mp hc
  exact ⟨u,hu⟩

lemma active_card_partition {V : Type} [Fintype V] [DecidableEq V]
    {W : Finset V} {p : Data V} (Q : Finset V)
    (hQ : ∀ v ∈ Q, p.1 v = 1 ∨ Hungry W p v) :
    (Q.filter (fun v => p.1 v = 1)).card + (Q.filter (Hungry W p)).card = Q.card := by
  classical
  have hd : Disjoint (Q.filter (fun v => p.1 v = 1)) (Q.filter (Hungry W p)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hh
    have hs := (Finset.mem_filter.mp hv).2
    have hlt := (Finset.mem_filter.mp hh).2.1
    rw [hs] at hlt; exact (lt_irrefl 1) hlt
  have hu : (Q.filter (fun v => p.1 v = 1)) ∪ (Q.filter (Hungry W p)) = Q := by
    ext v
    simp only [Finset.mem_union,Finset.mem_filter]
    constructor
    · tauto
    · intro hv; rcases hQ v hv with h | h
      · exact Or.inl ⟨hv,h⟩
      · exact Or.inr ⟨hv,h⟩
  rw [← Finset.card_union_of_disjoint hd,hu]

/-- Tameness bounds an active region by twice the congestion times its boundary.
All exits from the region, and all its sinks, must lie on that boundary. -/
theorem tame_region_card_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W : Finset V} {α : ℝ} {p : Data V}
    (hp : Cloud G W α p) (ht : Tame W α p) (hα : 1 ≤ 2*α)
    (Q D : Finset V) (hDQ : D ⊆ Q)
    (hQ : ∀ v ∈ Q, p.1 v = 1 ∨ Hungry W p v)
    (hW : ∀ v ∈ Q \ D, v ∉ W)
    (hout : ∀ v ∈ Q \ D, ∀ u ∉ Q, p.2 (v,u) = 0) :
    (Q.card : ℝ) ≤ 2*α*D.card := by
  classical
  let SQ := Q.filter (fun v => p.1 v = 1)
  let SD := D.filter (fun v => p.1 v = 1)
  let HQ := Q.filter (Hungry W p)
  let HD := D.filter (Hungry W p)
  have hSD : SD ⊆ SQ := Finset.filter_subset_filter _ hDQ
  have hHD : HD ⊆ HQ := Finset.filter_subset_filter _ hDQ
  have hsatI : ∀ v ∈ SQ \ SD, v ∈ Q \ D := by
    intro v hv
    obtain ⟨hvQ,hvs⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
    exact Finset.mem_sdiff.mpr ⟨hvQ,fun hvD => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨hvD,hvs⟩)⟩
  have hhunI : ∀ v ∈ HQ \ HD, v ∈ Q \ D := by
    intro v hv
    obtain ⟨hvQ,hvh⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
    exact Finset.mem_sdiff.mpr ⟨hvQ,fun hvD => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨hvD,hvh⟩)⟩
  have htarget : ∀ v ∈ Q \ D, ∀ u, 0 < p.2 (v,u) → u ∈ SQ := by
    intro v hv u hpos
    have huQ : u ∈ Q := by
      by_contra hn; have hz := hout v hv u hn; linarith
    exact Finset.mem_filter.mpr ⟨huQ,positive_flow_target_saturated hp ht hpos⟩
  have hsupply := supply_le_boundary_congestion hp SQ SD hSD
    (fun v hv => hW v (hsatI v hv)) (by
      intro v hv u hu
      apply le_antisymm _ (hp.flow (v,u))
      exact le_of_not_gt (fun hpos => hu (htarget v (hsatI v hv) u hpos)))
  have hsum : (∑ v ∈ SQ, p.1 v) = (SQ.card : ℝ) := by
    calc
      _ = ∑ _v ∈ SQ, (1 : ℝ) := Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = _ := by simp
  rw [hsum] at hsupply
  have hsucc : ∀ v : ↥(HQ \ HD), ∃ u : ↥SQ, 0 < p.2 (v.1,u.1) := by
    intro v
    have hvH := (Finset.mem_filter.mp (Finset.mem_sdiff.mp v.2).1).2
    obtain ⟨u,hu⟩ := hungry_has_positive_successor hp hvH (hW v (hhunI v v.2))
    exact ⟨⟨u,htarget v (hhunI v v.2) u hu⟩,hu⟩
  choose f hf using hsucc
  have hinj : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    have hvH := (Finset.mem_filter.mp (Finset.mem_sdiff.mp v.2).1).2
    have hwH := (Finset.mem_filter.mp (Finset.mem_sdiff.mp w.2).1).2
    have hwpos : 0 < p.2 (w.1,(f v).1) := by rw [he]; exact hf w
    exact ht.2.1 (f v).1 (Finset.mem_filter.mp (f v).2).2 v.1 w.1 hvH hwH (hf v) hwpos
  have hhun := Finset.card_le_card_of_injective hinj
  have hdiff := Finset.card_sdiff_add_card_eq_card hHD
  have hqp := active_card_partition Q hQ
  have hdp := active_card_partition D (fun v hv => hQ v (hDQ hv))
  have hhunR : (HQ.card : ℝ) ≤ (SQ.card : ℝ) + HD.card := by exact_mod_cast (show HQ.card ≤ SQ.card + HD.card by omega)
  have hqpR : (Q.card : ℝ) = SQ.card + HQ.card := by exact_mod_cast hqp.symm
  have hdpR : (D.card : ℝ) = SD.card + HD.card := by exact_mod_cast hdp.symm
  have hHDnonneg : (0 : ℝ) ≤ HD.card := Nat.cast_nonneg _
  rw [hqpR,hdpR]
  nlinarith

/-- The two conclusions of the cloud configuration contradict balance. -/
theorem configuration_contradiction {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W X B : Finset V} {a : ℕ} {α : ℝ} {p : Data V}
    (hp : Cloud G W α p) (ht : Tame W α p) (ha : 1 ≤ a)
    (hWcard : W.card = 14*a) (hWX : W ⊆ X) (hXB : Disjoint X B)
    (hactive : X = activeVertices W p) (hinactive : ∀ v ∉ X, p.1 v = 0)
    (hsupply : 14*(B.card : ℝ) < total p) (hαeq : α * a = 2 * (B.card : ℝ))
    (L S R : Finset V) (hpart : IsPartition3 (X ∪ B) L S R) (hno : NoEdge G L R)
    (hbal : 3*R.card ≤ 2*(X ∪ B).card) (hboundary : ((L ∩ W) ∪ (S ∩ X)).card ≤ a) : False := by
  classical
  let Q := (L ∪ S) ∩ X
  let D := (L ∩ W) ∪ (S ∩ X)
  have hDQ : D ⊆ Q := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp h).1,hWX (Finset.mem_inter.mp h).2⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp h).1,(Finset.mem_inter.mp h).2⟩
  have hQactive : ∀ v ∈ Q, p.1 v = 1 ∨ Hungry W p v := by
    intro v hv
    have hx := (Finset.mem_inter.mp hv).2
    rw [hactive] at hx
    exact (Finset.mem_filter.mp hx).2
  have hleft : (L ∪ S).card ≤ Q.card + B.card := by
    have hsub : L ∪ S ⊆ Q ∪ B := by
      intro v hv
      have hu : v ∈ X ∪ B := by rw [← hpart.2.2.2]; exact Finset.mem_union_left _ hv
      rcases Finset.mem_union.mp hu with hx | hb
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv,hx⟩)
      · exact Finset.mem_union_right _ hb
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le Q B)
  have hparts : (L ∪ S).card + R.card = (X ∪ B).card := by
    rw [← hpart.2.2.2,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hpart.2.1,hpart.2.2.1⟩)]
  have hUcard : (X ∪ B).card = X.card + B.card := Finset.card_union_of_disjoint hXB
  have htotal : total p ≤ (X.card : ℝ) := by
    have he : (∑ v ∈ X, p.1 v) = total p := Finset.sum_subset (Finset.subset_univ X)
      (fun v _ hv => hinactive v hv)
    rw [← he]
    calc
      _ ≤ ∑ _v ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun v _ => (hp.supply v).2)
      _ = _ := by simp
  have hα : 1 ≤ 2*α := by
    by_contra hn
    have hαsmall : α ≤ 1 := by linarith
    have he : X = W := by
      ext v
      rw [hactive]
      simpa only [activeVertices,Finset.mem_filter,Finset.mem_univ,true_and] using (ht.2.2 hαsmall).2 v
    have hQD : Q ⊆ D := by
      intro v hv
      obtain ⟨hls,hx⟩ := Finset.mem_inter.mp hv
      have hw : v ∈ W := he ▸ hx
      rcases Finset.mem_union.mp hls with hl | hs
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl,hw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hs,hx⟩)
    have hQa : Q.card ≤ a := (Finset.card_le_card hQD).trans hboundary
    have hXa : X.card = 14*a := he ▸ hWcard
    have hBa : B.card < a := by
      have hXreal : (X.card : ℝ) = 14*(a : ℝ) := by exact_mod_cast hXa
      have hb : (B.card : ℝ) < (a : ℝ) := by nlinarith
      exact_mod_cast hb
    omega
  have hQW : ∀ v ∈ Q \ D, v ∉ W := by
    intro v hv hw
    obtain ⟨hQ,hD⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hls,hx⟩ := Finset.mem_inter.mp hQ
    rcases Finset.mem_union.mp hls with hl | hs
    · exact hD (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hl,hw⟩))
    · exact hD (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hs,hx⟩))
  have hout : ∀ v ∈ Q \ D, ∀ u ∉ Q, p.2 (v,u) = 0 := by
    intro v hv u hu
    apply le_antisymm _ (hp.flow (v,u))
    apply le_of_not_gt
    intro hpos
    have hsatu := positive_flow_target_saturated hp ht hpos
    have huX : u ∈ X := by rw [hactive]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hsatu⟩
    obtain ⟨hvQ,hvD⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvLS,hvX⟩ := Finset.mem_inter.mp hvQ
    have hvL : v ∈ L := by
      rcases Finset.mem_union.mp hvLS with h | h
      · exact h
      · exact False.elim (hvD (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h,hvX⟩)))
    have huU : u ∈ L ∪ S ∪ R := by rw [hpart.2.2.2]; exact Finset.mem_union_left _ huX
    rcases Finset.mem_union.mp huU with hls | hr
    · exact hu (Finset.mem_inter.mpr ⟨hls,huX⟩)
    · have hz := hp.support v u (hno v hvL u hr); linarith
  have hcount := tame_region_card_bound hp ht hα Q D hDQ hQactive hQW hout
  have hDa : (D.card : ℝ) ≤ a := by exact_mod_cast hboundary
  have hscale := mul_le_mul_of_nonneg_left hDa (by linarith : 0 ≤ 2*α)
  have hQbound : (Q.card : ℝ) ≤ 4*(B.card : ℝ) := by nlinarith
  have hleftR : ((L ∪ S).card : ℝ) ≤ (Q.card : ℝ) + B.card := by exact_mod_cast hleft
  have hpartsR : ((L ∪ S).card : ℝ) + R.card = (X ∪ B).card := by exact_mod_cast hparts
  have hUcardR : ((X ∪ B).card : ℝ) = (X.card : ℝ) + B.card := by exact_mod_cast hUcard
  have hbalR : 3*(R.card : ℝ) ≤ 2*((X ∪ B).card : ℝ) := by exact_mod_cast hbal
  linarith

/-- Balanced separators of order `a` rule out a haven of order greater than `15a`. -/
theorem haven_order_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) : k ≤ 15*a := by
  classical
  by_contra hn
  have hk : 15*a < k := by omega
  obtain ⟨W,X,p,_,hWcard,hWX,hXB,hactive,_,_,_,_,hp,ht,hsupply,hinactive,L,S,R,hpart,hno,_,_,hbal,hboundary⟩ :=
    DvorakNorin2018.haven_cloud_balanced_configuration hβ hsep ha hk
  have hpG : Cloud G W (14*(β W).card/(7*(a : ℝ))) p := by
    refine ⟨hp.supply,hp.flow,?_,hp.sinks,hp.conserve,hp.bound⟩
    intro u v hn; exact hp.support u v (fun h => hn h.1)
  apply configuration_contradiction hpG ht ha hWcard hWX hXB hactive
    (fun v hv => (hinactive v hv).1) hsupply _ L S R hpart hno hbal hboundary
  have har : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  <;> ring
end StableMSR.Recovery.CloudCounting

open StableMSR.Recovery.Havens
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) : k ≤ 15*a := by
  exact StableMSR.Recovery.CloudCounting.haven_order_bound hβ hsep ha
