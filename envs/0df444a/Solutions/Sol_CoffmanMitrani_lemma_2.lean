-- Prove2me | solution 1 for CoffmanMitrani.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T15:14:44.701202+00:00
-- url     : https://prove2.me/submissions/d981899b-9fcf-4b38-843b-50c94826485d

import Mathlib
import Definitions.Def_CoffmanMitrani_Hss
import Definitions.Def_CoffmanMitrani_chain
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_Achieves
import Theorems.Thm_CoffmanMitrani_priority_achievable
import Theorems.Thm_CoffmanMitrani_chain_solution

set_option autoImplicit false

/-! Reduction of `CoffmanMitrani.lemma_2` (Coffman-Mitrani 1980, p. 817-818): every vertex of H** is a
preemptive priority vector. Children: `priority_achievable` (a priority strategy exists and achieves
some vector) and `chain_solution` (the priority vector is the unique solution of (5) on its chain).
Proved here: tight sets are nested (copy of our accepted tight_sets_nested proof), any two classes are
separated by a tight set at a vertex (else a perturbation direction exists), hence the tight sets form a
maximal chain = chain σ for the order "separated below". -/

open Finset

namespace CMPoly

open Finset

variable {n : ℕ}

/-- The polytope `H**` in generic form. -/
def K (ρ : Fin n → ℝ) (c : ℝ) (b : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {W | ∑ i, ρ i * W i = c ∧
    ∀ g : Finset (Fin n), g.Nonempty → g ≠ Finset.univ → b g ≤ ∑ i ∈ g, ρ i * W i}

theorem lin (ρ : Fin n → ℝ) (s : Finset (Fin n)) (W d : Fin n → ℝ) (t : ℝ) :
    ∑ i ∈ s, ρ i * (W + t • d) i = ∑ i ∈ s, ρ i * W i + t * ∑ i ∈ s, ρ i * d i := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- An extreme point admits no direction that keeps the conservation law and every tight
inequality. -/
theorem ext_rigid (ρ : Fin n → ℝ) (c : ℝ) (b : Finset (Fin n) → ℝ) (W : Fin n → ℝ)
    (hW : W ∈ (K ρ c b).extremePoints ℝ) (d : Fin n → ℝ)
    (hd0 : ∑ i, ρ i * d i = 0)
    (hdg : ∀ g : Finset (Fin n), g.Nonempty → g ≠ Finset.univ →
      ∑ i ∈ g, ρ i * W i = b g → ∑ i ∈ g, ρ i * d i = 0) :
    d = 0 := by
  have hWK := hW.1
  have hall : ∀ g : Finset (Fin n), ∀ᶠ t in nhds (0:ℝ),
      (g.Nonempty → g ≠ Finset.univ → b g ≤ ∑ i ∈ g, ρ i * (W + t • d) i) := by
    intro g
    by_cases hgt : g.Nonempty ∧ g ≠ Finset.univ
    · by_cases htight : ∑ i ∈ g, ρ i * W i = b g
      · refine Filter.Eventually.of_forall (fun t _ _ => ?_)
        rw [lin, hdg g hgt.1 hgt.2 htight, mul_zero, add_zero, htight]
      · have hlt : b g < ∑ i ∈ g, ρ i * W i :=
          lt_of_le_of_ne (hWK.2 g hgt.1 hgt.2) (Ne.symm htight)
        have hcont : Continuous fun t : ℝ =>
            ∑ i ∈ g, ρ i * W i + t * ∑ i ∈ g, ρ i * d i := by fun_prop
        have h0 := hcont.tendsto 0
        simp only [zero_mul, add_zero] at h0
        have hev := h0.eventually (lt_mem_nhds hlt)
        filter_upwards [hev] with t ht _ _
        rw [lin]
        exact ht.le
    · exact Filter.Eventually.of_forall (fun t h1 h2 => absurd ⟨h1, h2⟩ hgt)
  have hev : ∀ᶠ t in nhds (0:ℝ), W + t • d ∈ K ρ c b := by
    filter_upwards [Filter.eventually_all.mpr hall] with t ht
    refine ⟨?_, ht⟩
    rw [lin, hWK.1, hd0, mul_zero, add_zero]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have h1 : W + (ε / 2) • d ∈ K ρ c b := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith)
  have h2 : W + (-(ε / 2)) • d ∈ K ρ c b := hball (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]
    linarith)
  have hseg : W ∈ openSegment ℝ (W + (ε / 2) • d) (W + (-(ε / 2)) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : W + (ε / 2) • d = W := hW.2 h1 h2 hseg
  have h4 : (ε / 2) • d = 0 := by
    have := congrArg (fun v => v - W) h3
    simpa using this
  exact (smul_eq_zero.mp h4).resolve_left (by positivity)

end CMPoly

theorem cm_5a81ea39_key (x x1 x2 r r1 r2 : ℝ) (hx : 0 ≤ x) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hr : 0 ≤ r) (hr1 : 0 < r1) (hr2 : 0 < r2) (h : r + r1 + r2 < 1) :
    (x + x1) / (1 - (r + r1)) + (x + x2) / (1 - (r + r2)) <
      (x + x1 + x2) / (1 - (r + r1 + r2)) + x / (1 - r) := by
  have hD : 0 < 1 - r := by linarith
  have hD1 : 0 < 1 - (r + r1) := by linarith
  have hD2 : 0 < 1 - (r + r2) := by linarith
  have hD12 : 0 < 1 - (r + r1 + r2) := by linarith
  have e1 : (x + x1 + x2) / (1 - (r + r1 + r2)) - (x + x1) / (1 - (r + r1)) =
      x2 / (1 - (r + r1 + r2)) + (x + x1) * r2 / ((1 - (r + r1)) * (1 - (r + r1 + r2))) := by
    field_simp
    ring
  have e2 : (x + x2) / (1 - (r + r2)) - x / (1 - r) =
      x2 / (1 - (r + r2)) + x * r2 / ((1 - r) * (1 - (r + r2))) := by
    field_simp
    ring
  have i1 : x2 / (1 - (r + r2)) < x2 / (1 - (r + r1 + r2)) :=
    div_lt_div_of_pos_left hx2 hD12 (by linarith)
  have i2 : x * r2 / ((1 - r) * (1 - (r + r2))) ≤
      (x + x1) * r2 / ((1 - (r + r1)) * (1 - (r + r1 + r2))) := by
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hr2.le)
      (by positivity)
    exact mul_le_mul (by linarith) (by linarith) hD12.le hD.le
  linarith

theorem cm_5a81ea39_aux {ι : Type} [Fintype ι] [DecidableEq ι] (a r W : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hrho : ∀ i, 0 < r i) (hlt : ∑ i, r i < 1)
    (hcons : ∑ i, r i * W i = (∑ i, a i) / (1 - ∑ i, r i))
    (hineq : ∀ g : Finset ι, g.Nonempty → g ≠ Finset.univ →
      (∑ i ∈ g, a i) / (1 - ∑ i ∈ g, r i) ≤ ∑ i ∈ g, r i * W i)
    (g₁ g₂ : Finset ι) (hg₁ : g₁.Nonempty)
    (ht₁ : ∑ i ∈ g₁, r i * W i = (∑ i ∈ g₁, a i) / (1 - ∑ i ∈ g₁, r i))
    (ht₂ : ∑ i ∈ g₂, r i * W i = (∑ i ∈ g₂, a i) / (1 - ∑ i ∈ g₂, r i)) :
    g₁ ⊆ g₂ ∨ g₂ ⊆ g₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n21⟩ := hcon
  have hne1 : (g₁ \ g₂).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n12
  have hne2 : (g₂ \ g₁).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact n21
  have dec1 : ∀ c : ι → ℝ, ∑ i ∈ g₁, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i :=
    fun c => (Finset.sum_inter_add_sum_sdiff g₁ g₂ c).symm
  have dec2 : ∀ c : ι → ℝ, ∑ i ∈ g₂, c i = ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c; rw [Finset.inter_comm]; exact (Finset.sum_inter_add_sum_sdiff g₂ g₁ c).symm
  have decU : ∀ c : ι → ℝ, ∑ i ∈ g₁ ∪ g₂, c i =
      ∑ i ∈ g₁ ∩ g₂, c i + ∑ i ∈ g₁ \ g₂, c i + ∑ i ∈ g₂ \ g₁, c i := by
    intro c
    have := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := c)
    rw [dec1 c, dec2 c] at this
    linarith
  have hRlt : ∑ i ∈ g₁ ∪ g₂, r i < 1 := by
    have h1 : ∑ i ∈ g₁ ∪ g₂, r i ≤ ∑ i, r i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (hrho i).le)
    linarith
  have hU : (∑ i ∈ g₁ ∪ g₂, a i) / (1 - ∑ i ∈ g₁ ∪ g₂, r i) ≤
      ∑ i ∈ g₁ ∪ g₂, r i * W i := by
    by_cases hu : g₁ ∪ g₂ = Finset.univ
    · rw [hu, hcons]
    · exact hineq _ (hg₁.mono Finset.subset_union_left) hu
  have hI : (∑ i ∈ g₁ ∩ g₂, a i) / (1 - ∑ i ∈ g₁ ∩ g₂, r i) ≤
      ∑ i ∈ g₁ ∩ g₂, r i * W i := by
    rcases (g₁ ∩ g₂).eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · have hnu : g₁ ∩ g₂ ≠ Finset.univ := by
        intro hu
        apply n12
        intro x _
        have : x ∈ g₁ ∩ g₂ := hu ▸ Finset.mem_univ x
        exact (Finset.mem_inter.1 this).2
      exact hineq _ hne hnu
  have key := cm_5a81ea39_key (∑ i ∈ g₁ ∩ g₂, a i) (∑ i ∈ g₁ \ g₂, a i) (∑ i ∈ g₂ \ g₁, a i)
    (∑ i ∈ g₁ ∩ g₂, r i) (∑ i ∈ g₁ \ g₂, r i) (∑ i ∈ g₂ \ g₁, r i)
    (Finset.sum_nonneg fun i _ => (ha i).le) (Finset.sum_pos (fun i _ => ha i) hne1)
    (Finset.sum_pos (fun i _ => ha i) hne2) (Finset.sum_nonneg fun i _ => (hrho i).le)
    (Finset.sum_pos (fun i _ => hrho i) hne1) (Finset.sum_pos (fun i _ => hrho i) hne2)
    (by rw [← decU]; exact hRlt)
  rw [← decU a, ← decU r, ← dec1 a, ← dec1 r, ← dec2 a, ← dec2 r] at key
  have hS := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := fun i => r i * W i)
  linarith

open CoffmanMitrani in
theorem cm_tight_nested (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D)
    (g1 g2 : Finset (Fin D.M)) (hg1 : g1.Nonempty) (hg2 : g2.Nonempty)
    (ht1 : ∑ i ∈ g1, D.rho i * W i = D.loadBound g1)
    (ht2 : ∑ i ∈ g2, D.rho i * W i = D.loadBound g2) :
    g1 ⊆ g2 ∨ g2 ⊆ g1 := by
  have hpos : ∀ i, 0 < D.rho i := by
    intro i
    unfold Data.rho
    exact div_pos (D.lam_pos i) (D.mu_pos i)
  have hapos : ∀ i, 0 < D.rho i / D.mu i := fun i => div_pos (hpos i) (D.mu_pos i)
  obtain ⟨hc, hi⟩ := hW
  have hV : D.V = ∑ i, D.rho i / D.mu i := by
    unfold Data.V Data.rho
    apply Finset.sum_congr rfl
    intro i _
    rw [div_div, sq]
  have hlt : ∑ i, D.rho i < 1 := D.stable
  have hc' : ∑ i, D.rho i * W i = (∑ i, D.rho i / D.mu i) / (1 - ∑ i, D.rho i) := by
    rw [hc, hV]
  exact cm_5a81ea39_aux (fun i => D.rho i / D.mu i) D.rho W hapos hpos hlt hc'
    (fun g hg hgu => hi g hg hgu) g1 g2 hg1 ht1 ht2


namespace CM2

open CoffmanMitrani

def tightP (D : Data) (W : Fin D.M → ℝ) (g : Finset (Fin D.M)) : Prop :=
  g.Nonempty ∧ ∑ i ∈ g, D.rho i * W i = D.loadBound g

def prec (D : Data) (W : Fin D.M → ℝ) (a b : Fin D.M) : Prop :=
  ∃ g, tightP D W g ∧ a ∈ g ∧ b ∉ g

theorem rho_pos (D : Data) (i : Fin D.M) : 0 < D.rho i := by
  unfold Data.rho
  exact div_pos (D.lam_pos i) (D.mu_pos i)

theorem V_eq (D : Data) : D.V = ∑ i, D.rho i / D.mu i := by
  unfold Data.V Data.rho
  apply Finset.sum_congr rfl
  intro i _
  rw [div_div, sq]

theorem univ_tight (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D) :
    tightP D W Finset.univ := by
  refine ⟨Finset.univ_nonempty_iff.mpr ⟨⟨0, D.one_le_M⟩⟩, ?_⟩
  rw [hW.1, V_eq]
  rfl

theorem sep (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Set.extremePoints ℝ (Hss D))
    (a b : Fin D.M) (hab : a ≠ b) : prec D W a b ∨ prec D W b a := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hra : D.rho a * (1 / D.rho a) = 1 := mul_one_div_cancel (ne_of_gt (rho_pos D a))
  have hrb : D.rho b * (1 / D.rho b) = 1 := mul_one_div_cancel (ne_of_gt (rho_pos D b))
  let d : Fin D.M → ℝ := fun j =>
    (if j = a then 1 / D.rho a else 0) - (if j = b then 1 / D.rho b else 0)
  have hrd : ∀ j, D.rho j * d j = (if j = a then (1:ℝ) else 0) - (if j = b then (1:ℝ) else 0) := by
    intro j
    simp only [d, mul_sub, mul_ite, mul_zero]
    by_cases hja : j = a
    · subst hja
      rw [if_pos rfl, if_pos rfl, hra, if_neg hab, if_neg hab]
    · by_cases hjb : j = b
      · subst hjb
        rw [if_neg hja, if_neg hja, if_pos rfl, if_pos rfl, hrb]
      · rw [if_neg hja, if_neg hja, if_neg hjb, if_neg hjb]
  have hsum : ∀ s : Finset (Fin D.M), ∑ j ∈ s, D.rho j * d j =
      (if a ∈ s then (1:ℝ) else 0) - (if b ∈ s then (1:ℝ) else 0) := by
    intro s
    rw [Finset.sum_congr rfl (fun j _ => hrd j), Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
  have hd := CMPoly.ext_rigid D.rho (D.V / (1 - ∑ i, D.rho i)) D.loadBound W hW d (by
      rw [hsum, if_pos (Finset.mem_univ a), if_pos (Finset.mem_univ b), sub_self]) (by
      intro g hg _ ht
      rw [hsum]
      by_cases ha : a ∈ g
      · by_cases hb : b ∈ g
        · rw [if_pos ha, if_pos hb, sub_self]
        · exact absurd ⟨g, ⟨hg, ht⟩, ha, hb⟩ h1
      · by_cases hb : b ∈ g
        · exact absurd ⟨g, ⟨hg, ht⟩, hb, ha⟩ h2
        · rw [if_neg ha, if_neg hb, sub_self])
  have hda := congrFun hd a
  simp only [d, Pi.zero_apply, if_pos rfl, if_neg hab, sub_zero] at hda
  exact absurd hda (ne_of_gt (one_div_pos.mpr (rho_pos D a)))

theorem prec_trans (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D) (a b c : Fin D.M)
    (h1 : prec D W a b) (h2 : prec D W b c) : prec D W a c := by
  obtain ⟨g, hg, ha, hb⟩ := h1
  obtain ⟨g', hg', hb', hc⟩ := h2
  rcases cm_tight_nested D W hW g g' hg.1 hg'.1 hg.2 hg'.2 with hs | hs
  · exact ⟨g, hg, ha, fun hcg => hc (hs hcg)⟩
  · exact absurd (hs hb') hb

open Classical in
noncomputable def rk (D : Data) (W : Fin D.M → ℝ) (i : Fin D.M) : ℕ :=
  (Finset.univ.filter (fun j => prec D W j i)).card

theorem rk_lt (D : Data) (W : Fin D.M → ℝ) (i : Fin D.M) : rk D W i < D.M := by
  classical
  unfold rk
  calc _ < (Finset.univ : Finset (Fin D.M)).card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr
          ⟨i, Finset.mem_univ _, fun ⟨g, _, hi, hni⟩ => hni hi⟩)
    _ = D.M := by simp

theorem rk_mono (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Hss D) (a b : Fin D.M)
    (h : prec D W a b) : rk D W a < rk D W b := by
  classical
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun ⟨g, _, hi, hni⟩ => hni hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact prec_trans D W hW j a b hj h

theorem lemma2_core (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Set.extremePoints ℝ (Hss D)) :
    ∃ σ : Equiv.Perm (Fin D.M), ∀ k : Fin D.M,
      ∑ i ∈ chain σ k, D.rho i * W i = D.loadBound (chain σ k) := by
  have hWK : W ∈ Hss D := hW.1
  let rF : Fin D.M → Fin D.M := fun i => ⟨rk D W i, rk_lt D W i⟩
  have hinj : Function.Injective rF := by
    intro a b hab
    have hab' : rk D W a = rk D W b := congrArg Fin.val hab
    by_contra hne
    rcases sep D W hW a b hne with h | h
    · have := rk_mono D W hWK a b h
      omega
    · have := rk_mono D W hWK b a h
      omega
  let e := Equiv.ofBijective rF (Finite.injective_iff_bijective.mp hinj)
  refine ⟨e.symm, fun k => ?_⟩
  have hmem : ∀ a, a ∈ chain e.symm k ↔ rk D W a ≤ k.val := by
    intro a
    simp only [chain, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h3 : rF (e.symm l) = l := e.apply_symm_apply l
      have h4 : rk D W (e.symm l) = l.val := congrArg Fin.val h3
      rw [h4]
      exact hl
    · intro h
      refine ⟨rF a, h, ?_⟩
      exact e.symm_apply_apply a
  suffices hT : tightP D W (chain e.symm k) from hT.2
  by_cases htop : k.val + 1 = D.M
  · have hu : chain e.symm k = Finset.univ := by
      ext a
      rw [hmem]
      simp only [Finset.mem_univ, iff_true]
      have := rk_lt D W a
      omega
    rw [hu]
    exact univ_tight D W hWK
  · have hk1 : k.val + 1 < D.M := by
      have := k.isLt
      omega
    have hri : rF (e.symm k) = k := e.apply_symm_apply k
    have hrj : rF (e.symm ⟨k.val + 1, hk1⟩) = ⟨k.val + 1, hk1⟩ := e.apply_symm_apply _
    have e1 : rk D W (e.symm k) = k.val := congrArg Fin.val hri
    have e2 : rk D W (e.symm ⟨k.val + 1, hk1⟩) = k.val + 1 := congrArg Fin.val hrj
    have hij : e.symm k ≠ e.symm ⟨k.val + 1, hk1⟩ := by
      intro h
      rw [h] at e1
      omega
    have hprec : prec D W (e.symm k) (e.symm ⟨k.val + 1, hk1⟩) := by
      rcases sep D W hW _ _ hij with h | h
      · exact h
      · have := rk_mono D W hWK _ _ h
        omega
    obtain ⟨g, hgt, hig, hjg⟩ := hprec
    have hcg : chain e.symm k = g := by
      ext a
      rw [hmem]
      constructor
      · intro ha
        by_contra hag
        have := rk_mono D W hWK _ _ ⟨g, hgt, hig, hag⟩
        omega
      · intro hag
        have := rk_mono D W hWK _ _ ⟨g, hgt, hag, hjg⟩
        omega
    rw [hcg]
    exact hgt

end CM2

open CoffmanMitrani in
theorem solution (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Set.extremePoints ℝ (Hss D)) :
    ∃ (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M),
      IsPriority D σ S ∧ IsStrategy D S ∧ Achieves D S W := by
  obtain ⟨σ, hσ⟩ := CM2.lemma2_core D W hW
  obtain ⟨S, P, hP, hS, hA⟩ := priority_achievable D σ
  have hWP : W = P := (chain_solution D σ S P hP hS hA W).mp hσ
  subst hWP
  exact ⟨σ, S, hP, hS, hA⟩
