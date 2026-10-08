-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.theorem3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:27:04.650965+00:00
-- url     : https://prove2.me/submissions/32093fbe-4484-45e1-a595-4d948eef7abf

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

set_option autoImplicit false

namespace DW31Aux

open Set

lemma pos_near {g : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hg : ContinuousOn g (Ici 0)) (hpos : 0 < g x) :
    ∃ ε > 0, ∀ z ∈ Icc x (x + ε), 0 < g z := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuousOn_iff.1 hg x (mem_Ici.2 hx) (g x) hpos
  refine ⟨δ / 2, by linarith, fun z hz => ?_⟩
  have hz0 : z ∈ Ici (0:ℝ) := mem_Ici.2 (le_trans hx hz.1)
  have hd : dist z x < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2]
  have := H z hz0 hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

lemma le_of_Ioc {h : ℝ → ℝ} {s t K : ℝ} (hst : s < t) (hc : ContinuousOn h (Icc s t))
    (hK : ∀ u ∈ Ioc s t, K ≤ h u) : K ≤ h s := by
  by_contra H
  push Not at H
  obtain ⟨δ, hδ, Hd⟩ :=
    Metric.continuousOn_iff.1 hc s ⟨le_refl s, hst.le⟩ (K - h s) (by linarith)
  have hm1 : min (δ / 2) (t - s) ≤ δ / 2 := min_le_left _ _
  have hm2 : min (δ / 2) (t - s) ≤ t - s := min_le_right _ _
  have hm3 : 0 < min (δ / 2) (t - s) := lt_min (by linarith) (by linarith)
  have huI : s + min (δ / 2) (t - s) ∈ Ioc s t := ⟨by linarith, by linarith⟩
  have hd : dist (s + min (δ / 2) (t - s)) s < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have := Hd _ ⟨huI.1.le, huI.2⟩ hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [hK _ huI, this.2]

lemma last_time {P : ℝ → ℝ} {x z : ℝ} (hxz : x ≤ z) (hP : ContinuousOn P (Icc x z))
    (hx : P x ≤ 0) : ∃ w ∈ Icc x z, P w ≤ 0 ∧ ∀ u ∈ Ioc w z, 0 < P u := by
  have hAc : IsClosed (Icc x z ∩ P ⁻¹' Iic 0) :=
    hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAne : (Icc x z ∩ P ⁻¹' Iic 0).Nonempty := ⟨x, ⟨le_refl x, hxz⟩, hx⟩
  have hAb : BddAbove (Icc x z ∩ P ⁻¹' Iic 0) := ⟨z, fun u hu => hu.1.2⟩
  have hw : sSup (Icc x z ∩ P ⁻¹' Iic 0) ∈ Icc x z ∩ P ⁻¹' Iic 0 := hAc.csSup_mem hAne hAb
  refine ⟨_, hw.1, hw.2, fun u hu => ?_⟩
  by_contra H
  push Not at H
  have huA : u ∈ Icc x z ∩ P ⁻¹' Iic 0 := ⟨⟨le_trans hw.1.1 hu.1.le, hu.2⟩, H⟩
  have := le_csSup hAb huA
  linarith [hu.1]

lemma real_ind {f : ℝ → ℝ} {c s t : ℝ} (hst : s ≤ t) (hf : ContinuousOn f (Icc s t))
    (hloc : ∀ x ∈ Ico s t, 0 < f x → ∃ ε > 0, ∀ z ∈ Icc x (x + ε), f z ≤ f x - c * (z - x))
    (hpos : ∀ u ∈ Icc s t, 0 < f u) : f t ≤ f s - c * (t - s) := by
  have hcl : IsClosed ({u : ℝ | f u ≤ f s - c * (u - s)} ∩ Icc s t) := by
    have : {u : ℝ | f u ≤ f s - c * (u - s)} ∩ Icc s t =
        Icc s t ∩ (fun u => f u - (f s - c * (u - s))) ⁻¹' Iic 0 := by
      ext u
      simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    rw [this]
    apply ContinuousOn.preimage_isClosed_of_isClosed _ isClosed_Icc isClosed_Iic
    exact hf.sub (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
  have hsS : s ∈ {u : ℝ | f u ≤ f s - c * (u - s)} := by simp
  have key := hcl.Icc_subset_of_forall_exists_gt hsS (fun x hx y hy => by
    obtain ⟨hxS, hxI⟩ := hx
    have hxS' : f x ≤ f s - c * (x - s) := hxS
    obtain ⟨ε, hε, H⟩ := hloc x hxI (hpos x ⟨hxI.1, hxI.2.le⟩)
    have hy' : x < y := hy
    have hm1 : min ε (min (y - x) (t - x)) ≤ ε := min_le_left _ _
    have hm2 : min ε (min (y - x) (t - x)) ≤ y - x :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hm3 : 0 < min ε (min (y - x) (t - x)) :=
      lt_min hε (lt_min (by linarith) (by linarith [hxI.2]))
    refine ⟨x + min ε (min (y - x) (t - x)), ?_, by linarith, by linarith⟩
    have := H (x + min ε (min (y - x) (t - x))) ⟨by linarith, by linarith⟩
    show f _ ≤ f s - c * (_ - s)
    linarith)
  exact key ⟨hst, le_refl t⟩

lemma lip_cont {g : ℝ → ℝ} (hmono : MonotoneOn g (Ici 0))
    (hle : ∀ s t, 0 ≤ s → s ≤ t → g t - g s ≤ t - s) : ContinuousOn g (Ici 0) := by
  refine Metric.continuousOn_iff.2 fun x hx ε hε => ⟨ε, hε, fun y hy hxy => ?_⟩
  rw [Real.dist_eq, abs_lt] at hxy ⊢
  rcases le_total x y with h | h
  · have := hmono hx hy h
    have := hle x y (mem_Ici.1 hx) h
    constructor <;> linarith
  · have := hmono hy hx h
    have := hle y x (mem_Ici.1 hy) h
    constructor <;> linarith

theorem core (m0 m1 m2 : ℝ) (hm0 : 0 < m0) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (h1 : m0 + m2 < 1) (h2 : m1 < 1)
    (q0 q1 q2 a b d : ℝ → ℝ)
    (hq0 : ∀ t, 0 ≤ t → q0 t = q0 0 + t - a t / m0)
    (hq1 : ∀ t, 0 ≤ t → q1 t = q1 0 + a t / m0 - b t / m1)
    (hq2 : ∀ t, 0 ≤ t → q2 t = q2 0 + b t / m1 - d t / m2)
    (n0 : ∀ t, 0 ≤ t → 0 ≤ q0 t) (n1 : ∀ t, 0 ≤ t → 0 ≤ q1 t) (n2 : ∀ t, 0 ≤ t → 0 ≤ q2 t)
    (ha : MonotoneOn a (Ici 0)) (hb : MonotoneOn b (Ici 0)) (hd : MonotoneOn d (Ici 0))
    (hi0 : MonotoneOn (fun t => t - (a t + d t)) (Ici 0))
    (hi1 : MonotoneOn (fun t => t - b t) (Ici 0))
    (wc0 : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, 0 < q0 u + q2 u) →
      t - (a t + d t) = s - (a s + d s))
    (wc1 : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, 0 < q1 u) → t - b t = s - b s)
    (hsum : q0 0 + q1 0 + q2 0 = 1) :
    ∀ t, 2 / min (1 / (m0 + m2) - 1) (1 / m1 - 1) ≤ t → q0 t = 0 ∧ q1 t = 0 ∧ q2 t = 0 := by
  set ρ := m0 + m2 with hρ
  have hρpos : 0 < ρ := by linarith
  set c := min (1 / ρ - 1) (1 / m1 - 1) with hc
  have hc1 : 0 < 1 / ρ - 1 := by
    have : 1 < 1 / ρ := by rw [lt_div_iff₀ hρpos]; linarith
    linarith
  have hc2 : 0 < 1 / m1 - 1 := by
    have : 1 < 1 / m1 := by rw [lt_div_iff₀ hm1]; linarith
    linarith
  have hcpos : 0 < c := lt_min hc1 hc2
  have hcle1 : c ≤ 1 / ρ - 1 := min_le_left _ _
  have hcle2 : c ≤ 1 / m1 - 1 := min_le_right _ _
  set r := m2 / ρ with hr
  have hrpos : 0 < r := div_pos hm2 hρpos
  have hrlt : r < 1 := by rw [hr, div_lt_one hρpos]; linarith
  -- Lipschitz bounds
  have aL : ∀ s t, 0 ≤ s → s ≤ t → a t - a s ≤ t - s := by
    intro s t hs hst
    have h1' := hi0 (mem_Ici.2 hs) (mem_Ici.2 (le_trans hs hst)) hst
    have h2' := hd (mem_Ici.2 hs) (mem_Ici.2 (le_trans hs hst)) hst
    simp only at h1'
    linarith
  have dL : ∀ s t, 0 ≤ s → s ≤ t → d t - d s ≤ t - s := by
    intro s t hs hst
    have h1' := hi0 (mem_Ici.2 hs) (mem_Ici.2 (le_trans hs hst)) hst
    have h2' := ha (mem_Ici.2 hs) (mem_Ici.2 (le_trans hs hst)) hst
    simp only at h1'
    linarith
  have bL : ∀ s t, 0 ≤ s → s ≤ t → b t - b s ≤ t - s := by
    intro s t hs hst
    have h1' := hi1 (mem_Ici.2 hs) (mem_Ici.2 (le_trans hs hst)) hst
    simp only at h1'
    linarith
  have ac : ContinuousOn a (Ici 0) := lip_cont ha aL
  have bc : ContinuousOn b (Ici 0) := lip_cont hb bL
  have dc : ContinuousOn d (Ici 0) := lip_cont hd dL
  have q0c : ContinuousOn q0 (Ici 0) := by
    refine ContinuousOn.congr (f := fun t => q0 0 + t - a t / m0) ?_ (fun t ht => hq0 t ht)
    exact (continuousOn_const.add continuousOn_id).sub (ac.div_const m0)
  have q1c : ContinuousOn q1 (Ici 0) := by
    refine ContinuousOn.congr (f := fun t => q1 0 + a t / m0 - b t / m1) ?_ (fun t ht => hq1 t ht)
    exact (continuousOn_const.add (ac.div_const m0)).sub (bc.div_const m1)
  have q2c : ContinuousOn q2 (Ici 0) := by
    refine ContinuousOn.congr (f := fun t => q2 0 + b t / m1 - d t / m2) ?_ (fun t ht => hq2 t ht)
    exact (continuousOn_const.add (bc.div_const m1)).sub (dc.div_const m2)
  set G1 : ℝ → ℝ := fun t => q0 t + r * (q1 t + q2 t) with hG1def
  set G2 : ℝ → ℝ := fun t => q0 t + q1 t with hG2def
  set F : ℝ → ℝ := fun t => max (G1 t) (G2 t) with hFdef
  have G1c : ContinuousOn G1 (Ici 0) := q0c.add (continuousOn_const.mul (q1c.add q2c))
  have G2c : ContinuousOn G2 (Ici 0) := q0c.add q1c
  have Fc : ContinuousOn F (Ici 0) := G1c.sup G2c
  have q02c : ContinuousOn (fun u => q0 u + q2 u) (Ici 0) := q0c.add q2c
  -- increments
  have hG1 : ∀ s t, 0 ≤ s → s ≤ t →
      G1 t - G1 s = (t - s) - ((a t + d t) - (a s + d s)) / ρ := by
    intro s t hs hst
    have ht : 0 ≤ t := le_trans hs hst
    simp only [hG1def]
    rw [hq0 t ht, hq0 s hs, hq1 t ht, hq1 s hs, hq2 t ht, hq2 s hs, hr, hρ]
    field_simp
    ring
  have hG2 : ∀ s t, 0 ≤ s → s ≤ t → G2 t - G2 s = (t - s) - (b t - b s) / m1 := by
    intro s t hs hst
    have ht : 0 ≤ t := le_trans hs hst
    simp only [hG2def]
    rw [hq0 t ht, hq0 s hs, hq1 t ht, hq1 s hs]
    field_simp
    ring
  have G1up : ∀ s t, 0 ≤ s → s ≤ t → G1 t ≤ G1 s + (t - s) := by
    intro s t hs hst
    have ht : 0 ≤ t := le_trans hs hst
    have e := hG1 s t hs hst
    have h3 := ha (mem_Ici.2 hs) (mem_Ici.2 ht) hst
    have h4 := hd (mem_Ici.2 hs) (mem_Ici.2 ht) hst
    have : 0 ≤ ((a t + d t) - (a s + d s)) / ρ := div_nonneg (by linarith) hρpos.le
    linarith
  have G1down : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, 0 < q0 u + q2 u) →
      G1 t ≤ G1 s - c * (t - s) := by
    intro s t hs hst hpos
    have e := hG1 s t hs hst
    have w := wc0 s t hs hst hpos
    have hΔ : (a t + d t) - (a s + d s) = t - s := by linarith
    rw [hΔ] at e
    have e2 : G1 t - G1 s = -((1 / ρ - 1) * (t - s)) := by rw [e]; ring
    have : c * (t - s) ≤ (1 / ρ - 1) * (t - s) :=
      mul_le_mul_of_nonneg_right hcle1 (by linarith)
    linarith
  have G2down : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Ioc s t, 0 < q1 u) →
      G2 t ≤ G2 s - c * (t - s) := by
    intro s t hs hst hpos
    have ht : 0 ≤ t := le_trans hs hst
    have hid : t - b t = s - b s := by
      rcases eq_or_lt_of_le hst with h | h
      · rw [h]
      · have le1 : t - b t ≤ s - b s := by
          refine le_of_Ioc (h := fun u => u - b u) h ?_ ?_
          · exact (continuousOn_id.sub bc).mono (fun u hu => mem_Ici.2 (le_trans hs hu.1))
          · intro u hu
            have := wc1 u t (le_trans hs hu.1.le) hu.2
              (fun v hv => hpos v ⟨lt_of_lt_of_le hu.1 hv.1, hv.2⟩)
            show t - b t ≤ u - b u
            linarith
        have le2 := hi1 (mem_Ici.2 hs) (mem_Ici.2 ht) hst
        simp only at le2
        linarith
    have e := hG2 s t hs hst
    have hΔ : b t - b s = t - s := by linarith
    rw [hΔ] at e
    have e2 : G2 t - G2 s = -((1 / m1 - 1) * (t - s)) := by rw [e]; ring
    have : c * (t - s) ≤ (1 / m1 - 1) * (t - s) :=
      mul_le_mul_of_nonneg_right hcle2 (by linarith)
    linarith
  -- algebraic relations
  have relC : ∀ u, 0 ≤ u → G1 u < G2 u → 0 < q1 u := by
    intro u hu h
    simp only [hG1def, hG2def] at h
    have h0 := n2 u hu
    by_contra H
    push Not at H
    have : q1 u = 0 := le_antisymm H (n1 u hu)
    rw [this] at h
    have : 0 ≤ r * q2 u := mul_nonneg hrpos.le h0
    linarith
  have relD : ∀ u, 0 ≤ u → 0 < F u → G2 u ≤ G1 u → 0 < q0 u + q2 u := by
    intro u hu hF h
    simp only [hFdef, hG1def, hG2def] at hF h
    by_contra H
    push Not at H
    have e0 : q0 u = 0 := le_antisymm (by linarith [n2 u hu]) (n0 u hu)
    have e2 : q2 u = 0 := le_antisymm (by linarith [n0 u hu]) (n2 u hu)
    rw [e0, e2] at h hF
    have h1u := n1 u hu
    have : q1 u * (1 - r) ≤ 0 := by nlinarith
    have : q1 u = 0 := by
      rcases eq_or_lt_of_le h1u with h' | h'
      · exact h'.symm
      · have : 0 < q1 u * (1 - r) := mul_pos h' (by linarith)
        linarith
    rw [this] at hF
    simp at hF
  have relE : ∀ u, 0 ≤ u → F u ≤ 0 → q0 u = 0 ∧ q1 u = 0 ∧ q2 u = 0 := by
    intro u hu hF
    simp only [hFdef, hG1def, hG2def, max_le_iff] at hF
    obtain ⟨hA, hB⟩ := hF
    have z0 := n0 u hu
    have z1 := n1 u hu
    have z2 := n2 u hu
    have e0 : q0 u = 0 := by linarith
    have e1 : q1 u = 0 := by linarith
    refine ⟨e0, e1, ?_⟩
    rw [e0, e1] at hA
    have : r * q2 u ≤ 0 := by linarith
    have : q2 u ≤ 0 := by
      by_contra H
      push Not at H
      have := mul_pos hrpos H
      linarith
    linarith
  have F0 : F 0 ≤ 1 := by
    simp only [hFdef, hG1def, hG2def, max_le_iff]
    have z0 := n0 0 le_rfl
    have z1 := n1 0 le_rfl
    have z2 := n2 0 le_rfl
    constructor
    · have : r * (q1 0 + q2 0) ≤ q1 0 + q2 0 := by
        have := mul_le_mul_of_nonneg_right hrlt.le (by linarith : 0 ≤ q1 0 + q2 0)
        linarith
      linarith
    · linarith
  -- local decrease
  have loc : ∀ x, 0 ≤ x → 0 < F x →
      ∃ ε > 0, ∀ z ∈ Icc x (x + ε), F z ≤ F x - c * (z - x) := by
    intro x hx hFx
    rcases lt_or_ge (G1 x) (G2 x) with hlt | hle
    · have hq1x := relC x hx hlt
      obtain ⟨ε1, hε1, H1⟩ := pos_near hx q1c hq1x
      have hFx' : F x = G2 x := max_eq_right hlt.le
      refine ⟨min ε1 ((G2 x - G1 x) / (1 + c)), lt_min hε1 (div_pos (by linarith) (by linarith)),
        fun z hz => ?_⟩
      have hzε1 : z ≤ x + ε1 := le_trans hz.2 (by linarith [min_le_left ε1 ((G2 x - G1 x) / (1 + c))])
      have hzη : z - x ≤ (G2 x - G1 x) / (1 + c) := by
        linarith [hz.2, min_le_right ε1 ((G2 x - G1 x) / (1 + c))]
      have hzη' : (z - x) * (1 + c) ≤ G2 x - G1 x := (le_div_iff₀ (by linarith)).1 hzη
      have g2 := G2down x z hx hz.1 (fun u hu => H1 u ⟨hu.1.le, le_trans hu.2 hzε1⟩)
      have g1 := G1up x z hx hz.1
      rw [hFx']
      show max (G1 z) (G2 z) ≤ _
      apply max_le
      · nlinarith
      · exact g2
    · have hpos := relD x hx hFx hle
      obtain ⟨ε, hε, H⟩ := pos_near hx q02c hpos
      have hFx' : F x = G1 x := max_eq_left hle
      refine ⟨ε, hε, fun z hz => ?_⟩
      have g1 := G1down x z hx hz.1 (fun u hu => H u ⟨hu.1, le_trans hu.2 hz.2⟩)
      rw [hFx']
      show max (G1 z) (G2 z) ≤ _
      apply max_le g1
      -- last time G2 ≤ G1 on [x, z]
      have hPc : ContinuousOn (fun u => G2 u - G1 u) (Icc x z) :=
        (G2c.sub G1c).mono (fun u hu => mem_Ici.2 (le_trans hx hu.1))
      obtain ⟨w, hw, hPw, hPafter⟩ := last_time hz.1 hPc (by show G2 x - G1 x ≤ 0; linarith)
      have hw0 : 0 ≤ w := le_trans hx hw.1
      have g2 := G2down w z hw0 hw.2 (fun u hu => relC u (le_trans hw0 hu.1.le)
        (by have : 0 < G2 u - G1 u := hPafter u hu; linarith))
      have g1w := G1down x w hx hw.1 (fun u hu => H u ⟨hu.1, le_trans hu.2 (le_trans hw.2 hz.2)⟩)
      have hPw' : G2 w - G1 w ≤ 0 := hPw
      nlinarith
  have mainIcc : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, 0 < F u) →
      F t ≤ F s - c * (t - s) := by
    intro s t hs hst hpos
    exact real_ind hst (Fc.mono (fun u hu => mem_Ici.2 (le_trans hs hu.1)))
      (fun x hx hFx => loc x (le_trans hs hx.1) hFx) hpos
  have mainIoc : ∀ s t, 0 ≤ s → s < t → (∀ u ∈ Ioc s t, 0 < F u) →
      F t ≤ F s - c * (t - s) := by
    intro s t hs hst hpos
    refine le_of_Ioc (h := fun u => F u - c * (t - u)) hst ?_ ?_
    · exact (Fc.mono (fun u hu => mem_Ici.2 (le_trans hs hu.1))).sub
        (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
    · intro u hu
      exact mainIcc u t (le_trans hs hu.1.le) hu.2
        (fun v hv => hpos v ⟨lt_of_lt_of_le hu.1 hv.1, hv.2⟩)
  -- conclusion
  intro t ht
  have hδ : 0 < 2 / c := div_pos (by norm_num) hcpos
  have ht0 : 0 ≤ t := le_trans hδ.le ht
  apply relE t ht0
  by_contra hFt
  push Not at hFt
  by_cases hz : ∃ u ∈ Icc 0 t, F u ≤ 0
  · obtain ⟨u, hu, hFu⟩ := hz
    obtain ⟨w, hw, hFw, hafter⟩ := last_time hu.2
      (Fc.mono (fun v hv => mem_Ici.2 (le_trans hu.1 hv.1))) hFu
    have hwt : w < t := by
      rcases eq_or_lt_of_le hw.2 with h | h
      · rw [h] at hFw; linarith
      · exact h
    have := mainIoc w t (le_trans hu.1 hw.1) hwt hafter
    have : 0 ≤ c * (t - w) := mul_nonneg hcpos.le (by linarith)
    linarith
  · push Not at hz
    have := mainIcc 0 t le_rfl ht0 hz
    have hct : 2 ≤ c * t := by
      have := mul_le_mul_of_nonneg_left ht hcpos.le
      rwa [mul_div_cancel₀ _ hcpos.ne'] at this
    linarith

end DW31Aux

open DW31Aux in
open DaiWeissFluid.ThreeBuffer in
theorem solution (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1) :
    FluidStable (threeBuffer m).IsWorkConserving := by
  have hcpos : 0 < min (1 / (m 0 + m 2) - 1) (1 / m 1 - 1) := by
    have hρpos : 0 < m 0 + m 2 := by linarith [hm 0, hm 2]
    refine lt_min ?_ ?_
    · have : 1 < 1 / (m 0 + m 2) := by rw [lt_div_iff₀ hρpos]; linarith
      linarith
    · have : 1 < 1 / m 1 := by rw [lt_div_iff₀ (hm 1)]; linarith
      linarith
  refine ⟨2 / min (1 / (m 0 + m 2) - 1) (1 / m 1 - 1), div_pos (by norm_num) hcpos,
    fun Q T hQT hsum t ht k => ?_⟩
  obtain ⟨hsol, hwc⟩ := hQT
  have hC0 : ∀ g : Fin 3 → ℝ, ∑ k ∈ (threeBuffer m).C 0, g k = g 0 + g 2 := by
    intro g
    unfold ReentrantLine.C
    rw [Finset.sum_filter, Fin.sum_univ_three]
    simp [threeBuffer, Fin.ext_iff]
  have hC1 : ∀ g : Fin 3 → ℝ, ∑ k ∈ (threeBuffer m).C 1, g k = g 1 := by
    intro g
    unfold ReentrantLine.C
    rw [Finset.sum_filter, Fin.sum_univ_three]
    simp [threeBuffer, Fin.ext_iff]
  have hidle0 : (threeBuffer m).idle T 0 = fun t => t - (T t 0 + T t 2) := by
    funext t
    simp only [ReentrantLine.idle, ReentrantLine.busy]
    rw [hC0 (fun k => T t k)]
  have hidle1 : (threeBuffer m).idle T 1 = fun t => t - T t 1 := by
    funext t
    simp only [ReentrantLine.idle, ReentrantLine.busy]
    rw [hC1 (fun k => T t k)]
  have hfl0 : ∀ t, 0 ≤ t → Q t 0 = Q 0 0 + t - T t 0 / m 0 := by
    intro t ht
    have := hsol.flow t ht 0
    rw [this]
    simp [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer]
    ring
  have hfl1 : ∀ t, 0 ≤ t → Q t 1 = Q 0 1 + T t 0 / m 0 - T t 1 / m 1 := by
    intro t ht
    have := hsol.flow t ht 1
    rw [this]
    simp [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer]
    ring
  have hfl2 : ∀ t, 0 ≤ t → Q t 2 = Q 0 2 + T t 1 / m 1 - T t 2 / m 2 := by
    intro t ht
    have := hsol.flow t ht 2
    rw [this]
    simp [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer]
    ring
  have hw0 := hwc 0
  have hw1 := hwc 1
  rw [hidle0] at hw0
  rw [hidle1] at hw1
  have hi0 := hsol.idle_mono 0
  have hi1 := hsol.idle_mono 1
  rw [hidle0] at hi0
  rw [hidle1] at hi1
  have key := core (m 0) (m 1) (m 2) (hm 0) (hm 1) (hm 2) h1 h2
    (fun t => Q t 0) (fun t => Q t 1) (fun t => Q t 2)
    (fun t => T t 0) (fun t => T t 1) (fun t => T t 2)
    hfl0 hfl1 hfl2
    (fun t ht => hsol.nonneg t ht 0) (fun t ht => hsol.nonneg t ht 1)
    (fun t ht => hsol.nonneg t ht 2)
    (hsol.T_mono 0) (hsol.T_mono 1) (hsol.T_mono 2) hi0 hi1
    (fun s t hs hst hpos => hw0 s t hs hst (fun u hu => by show 0 < ∑ k ∈ (threeBuffer m).C 0, Q u k; rw [hC0 (fun k => Q u k)]; exact hpos u hu))
    (fun s t hs hst hpos => hw1 s t hs hst (fun u hu => by show 0 < ∑ k ∈ (threeBuffer m).C 1, Q u k; rw [hC1 (fun k => Q u k)]; exact hpos u hu))
    (by have := hsum; simp only [Fin.sum_univ_three] at this; exact this) t ht
  fin_cases k
  · exact key.1
  · exact key.2.1
  · exact key.2.2
