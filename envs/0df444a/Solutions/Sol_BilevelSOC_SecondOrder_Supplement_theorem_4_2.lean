-- Prove2me | solution 1 for BilevelSOC.SecondOrder.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:39.172847+00:00
-- url     : https://prove2.me/submissions/3fc1c2be-297e-4e56-bb6d-730c887e1a28

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_ValueCriteria
open scoped Topology

open BilevelSOC
open BilevelSOC.SecondOrder
open BilevelSOC.SecondOrder.Supplement

theorem solution {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hbounded : LowerLocallyBounded D z.1)
    (hMFCQ : ∀ y ∈ solMap D z.1, LMFCQ D (z.1, y))
    (hexclude : ∀ d, valueSystem D z d → d = 0) :
    StrictLocalMin D.F (feasSet D) z := by
      open Filter Set in
      classical
      have hdiff : ∀ (h : E n × Y m → ℝ) (a : E n × Y m), ContDiff ℝ 2 h →
          ∀ (u v : ℕ → E n × Y m) (c : ℕ → ℝ) (w : E n × Y m),
          Tendsto u atTop (𝓝 a) → Tendsto v atTop (𝓝 a) →
          Tendsto (fun k => c k • (u k - v k)) atTop (𝓝 w) →
          Tendsto (fun k => c k * (h (u k) - h (v k))) atTop
            (𝓝 (fderiv ℝ h a w)) := by
        intro h a hh u v c w hu hv hw
        have hs := (hh.hasStrictFDerivAt (x := a) (by norm_num)).isLittleOTVS
        have he := (hs.comp_tendsto (hu.prodMk_nhds hv)).smul_left c
        rw [Asymptotics.isLittleOTVS_iff_isLittleO] at he
        have he' := he.trans_isBigO (hw.isBigO_one ℝ)
        rw [Asymptotics.isLittleO_one_iff ℝ] at he'
        have hlin := ((fderiv ℝ h a).continuous.tendsto w).comp hw
        convert he'.add hlin using 1 <;> simp [smul_sub]
        funext k
        ring
      refine ⟨hfeas, ?_⟩
      by_contra hnot
      have hcl : z ∈ closure {a | a ∈ feasSet D ∧ D.F a ≤ D.F z ∧ a ≠ z} := by
        rw [mem_closure_iff_nhds]
        intro U hU
        by_contra hh
        apply hnot
        refine ⟨U, hU, ?_⟩
        intro a ha hne
        have : ¬ D.F a ≤ D.F z := by
          intro hle
          exact hh ⟨a, ha.2, ha.1, hle, hne⟩
        exact lt_of_not_ge this
      obtain ⟨a, ha, haz⟩ := mem_closure_iff_seq_limit.mp hcl
      let t : ℕ → ℝ := fun k => ‖a k - z‖
      let v : ℕ → E n × Y m := fun k => (t k)⁻¹ • (a k - z)
      have htpos : ∀ k, 0 < t k := fun k => norm_pos_iff.mpr (sub_ne_zero.mpr (ha k).2.2)
      have ht : Tendsto t atTop (𝓝 0) := by
        simpa [t] using (haz.sub (tendsto_const_nhds (x := z))).norm
      have hvnorm : ∀ k, ‖v k‖ = 1 := by
        intro k
        simp [v, norm_smul, t, ne_of_gt (htpos k)]
      obtain ⟨d, hd, φ, hφ, hv⟩ := (isCompact_sphere (0 : E n × Y m) 1).tendsto_subseq
        (fun k => by simpa [Metric.mem_sphere, dist_zero_right] using hvnorm k)
      have hdnorm : ‖d‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hd
      have hφt := hφ.tendsto_atTop
      have heq : ∀ k, z + t k • v k = a k := by
        intro k
        simp [v, smul_smul, ne_of_gt (htpos k)]
      have hdir : ∀ (h : E n × Y m → ℝ), ContDiff ℝ 2 h →
          Tendsto (fun k => (t (φ k))⁻¹ * (h (a (φ k)) - h z)) atTop
            (𝓝 (fderiv ℝ h z d)) := by
        intro h hh
        apply hdiff h z hh (a ∘ φ) (fun _ => z) (fun k => (t (φ k))⁻¹) d
          (haz.comp hφt) tendsto_const_nhds
        exact hv
      have hle : ∀ (h : E n × Y m → ℝ), ContDiff ℝ 2 h →
          (∀ k, h (a k) ≤ h z) → fderiv ℝ h z d ≤ 0 := by
        intro h hh hineq
        exact le_of_tendsto (hdir h hh) (Eventually.of_forall fun k =>
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr (htpos _))) (sub_nonpos.mpr (hineq _)))
      have hF : fderiv ℝ D.F z d ≤ 0 := hle _ hStanding.1 (fun k => (ha k).2.1)
      have hG : ∀ i ∈ actG D z, fderiv ℝ (D.G i) z d ≤ 0 := by
        intro i hi
        apply hle _ (hStanding.2.2.1 i)
        intro k
        simpa [show D.G i z = 0 from hi] using (ha k).1.1 i
      have hg : ∀ i ∈ actg D z, fderiv ℝ (D.g i) z d ≤ 0 := by
        intro i hi
        apply hle _ (hStanding.2.2.2 i)
        intro k
        simpa [show D.g i z = 0 from hi] using (ha k).1.2.1 i
      have hval : (fderiv ℝ D.f z d : EReal) ≤ upperDini (valueFn D) z.1 d.1 := by
        by_contra hvalnot
        obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hvalnot)
        have hrf : r < fderiv ℝ D.f z d := EReal.coe_lt_coe_iff.mp hr'
        have hquot : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
            dirQuot (valueFn D) z.1 d.1 s < (r : EReal) :=
          eventually_lt_of_limsup_lt hr
        have hbase : valueFn D z.1 = (D.f z : EReal) := by
          apply le_antisymm
          · exact iInf_le_of_le z.2 (iInf_le_of_le hfeas.2.1 le_rfl)
          · exact le_iInf fun y => le_iInf fun hy => EReal.coe_le_coe_iff.mpr (hfeas.2.2 y hy)
        let T : ℕ → ℝ := fun k => t (φ k)
        let X : ℕ → E n × Y m := fun k => a (φ k)
        have hT : Tendsto T atTop (𝓝 0) := ht.comp hφt
        have hTpos : ∀ k, 0 < T k := fun k => htpos _
        have hXT : Tendsto X atTop (𝓝 z) := haz.comp hφt
        have hTwithin : Tendsto T atTop (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsWithin_iff.mpr ⟨hT, Eventually.of_forall hTpos⟩
        have hex : ∀ᶠ k in atTop, ∃ y ∈ lowerFeas D (z.1 + T k • d.1),
            D.f (z.1 + T k • d.1, y) < D.f z + T k * r := by
          filter_upwards [hTwithin.eventually hquot] with k hk
          by_contra hn
          have hvlow : (D.f z + T k * r : EReal) ≤ valueFn D (z.1 + T k • d.1) := by
            apply le_iInf
            intro y
            apply le_iInf
            intro hy
            exact EReal.coe_le_coe_iff.mpr (not_lt.mp (fun hh => hn ⟨y, hy, hh⟩))
          have hsub := EReal.sub_le_sub hvlow (le_refl (D.f z : EReal))
          have hmul := mul_le_mul_of_nonneg_left hsub
            (show (0 : EReal) ≤ ((T k)⁻¹ : ℝ) from EReal.coe_nonneg.mpr (inv_nonneg.mpr (hTpos k).le))
          have he : (((T k)⁻¹ : ℝ) : EReal) *
              ((D.f z + T k * r : ℝ) - D.f z) = (r : EReal) := by
            rw [← EReal.coe_sub, ← EReal.coe_mul]
            congr 1
            field_simp [ne_of_gt (hTpos k)]
            ring
          have he' : (((T k)⁻¹ : ℝ) : EReal) *
              ((D.f z : EReal) + (T k : EReal) * (r : EReal) - D.f z) = (r : EReal) := by
            simpa only [EReal.coe_add, EReal.coe_mul] using he
          rw [he'] at hmul
          exact (not_le_of_gt hk) (by simpa [dirQuot, hbase] using hmul)
        choose y hy using (fun k => show ∃ y : Y m,
            (∃ y ∈ lowerFeas D (z.1 + T k • d.1),
              D.f (z.1 + T k • d.1, y) < D.f z + T k * r) →
            y ∈ lowerFeas D (z.1 + T k • d.1) ∧
              D.f (z.1 + T k • d.1, y) < D.f z + T k * r from by
          by_cases hh : ∃ y ∈ lowerFeas D (z.1 + T k • d.1),
              D.f (z.1 + T k • d.1, y) < D.f z + T k * r
          · obtain ⟨y, hy, hf⟩ := hh
            exact ⟨y, fun _ => ⟨hy, hf⟩⟩
          · exact ⟨0, fun h => False.elim (hh h)⟩)
        have hygood : ∀ᶠ k in atTop, y k ∈ lowerFeas D (z.1 + T k • d.1) ∧
            D.f (z.1 + T k • d.1, y k) < D.f z + T k * r := by
          filter_upwards [hex] with k hk using hy k hk
        have hparam : Tendsto (fun k => z.1 + T k • d.1) atTop (𝓝 z.1) := by
          simpa using tendsto_const_nhds.add (hT.smul_const d.1)
        obtain ⟨U, hU, B, hB, hbound⟩ := hbounded
        have hyB : ∀ᶠ k in atTop, y k ∈ closure B := by
          filter_upwards [hygood, hparam.eventually hU] with k hk hku
          exact subset_closure (hbound _ hku hk.1)
        obtain ⟨ystar, hystar, ψ, hψ, hyconv⟩ := hB.isCompact_closure.tendsto_subseq' hyB.frequently
        have hψt := hψ.tendsto_atTop
        let b : ℕ → E n × Y m := fun k => (z.1 + T (ψ k) • d.1, y (ψ k))
        have hb : Tendsto b atTop (𝓝 (z.1, ystar)) :=
          (hparam.comp hψt).prodMk_nhds hyconv
        have hbgood : ∀ᶠ k in atTop, y (ψ k) ∈ lowerFeas D (b k).1 ∧
            D.f (b k) < D.f z + T (ψ k) * r := hψt.eventually hygood
        have hbfeas : ystar ∈ lowerFeas D z.1 := by
          intro i
          exact le_of_tendsto ((hStanding.2.2.2 i).continuous.continuousAt.tendsto.comp hb)
            (hbgood.mono fun k hk => hk.1 i)
        have hbf : D.f (z.1, ystar) ≤ D.f z := by
          have hfconv := hStanding.2.1.continuous.continuousAt.tendsto.comp hb
          have hupper : Tendsto (fun k => D.f z + T (ψ k) * r) atTop (𝓝 (D.f z)) := by
            simpa using tendsto_const_nhds.add ((hT.comp hψt).mul_const r)
          exact le_of_tendsto_of_tendsto hfconv hupper (hbgood.mono fun k hk => hk.2.le)
        have hsol : ystar ∈ solMap D z.1 :=
          ⟨hbfeas, fun y hy => hbf.trans (hfeas.2.2 y hy)⟩
        obtain ⟨w, hw⟩ := hMFCQ ystar hsol
        let L : ℝ := fderiv ℝ D.f (z.1, ystar) (0, w)
        let ε : ℝ := (fderiv ℝ D.f z d - r) / (2 * (|L| + 1))
        have hε : 0 < ε := div_pos (sub_pos.mpr hrf) (by positivity)
        have hεL : r + ε * L < fderiv ℝ D.f z d := by
          have ha : L ≤ |L| := le_abs_self L
          have heq : ε * (2 * (|L| + 1)) = fderiv ℝ D.f z d - r := by
            dsimp [ε]
            field_simp
          nlinarith [abs_nonneg L]
        let c : ℕ → E n × Y m := fun k => ((X (ψ k)).1, y (ψ k) + T (ψ k) • (ε • w))
        have hc : Tendsto c atTop (𝓝 (z.1, ystar)) := by
          apply ((hXT.comp hψt).fst_nhds).prodMk_nhds
          simpa using hyconv.add ((hT.comp hψt).smul_const (ε • w))
        have hscaled : Tendsto (fun k => (T (ψ k))⁻¹ • (c k - b k)) atTop (𝓝 (0, ε • w)) := by
          have hvfirst := (hv.comp hψt).fst_nhds.sub_const d.1
          have heq' : (fun k => (T (ψ k))⁻¹ • (c k - b k)) =
              (fun k => ((v (φ (ψ k))).1 - d.1, ε • w)) := by
            funext k
            have hx : X (ψ k) = z + T (ψ k) • v (φ (ψ k)) := (heq _).symm
            ext <;> simp [c, b, hx, Prod.smul_mk, smul_sub, smul_smul, ne_of_gt (hTpos _)]
          rw [heq']
          simpa using hvfirst.prodMk_nhds (tendsto_const_nhds (x := ε • w))
        have hcfeas : ∀ᶠ k in atTop, (c k).2 ∈ lowerFeas D (c k).1 := by
          rw [show (fun k => (c k).2 ∈ lowerFeas D (c k).1) =
              (fun k => ∀ i, D.g i (c k) ≤ 0) from rfl]
          apply (eventually_all.mpr ?_)
          intro i
          by_cases hi : D.g i (z.1, ystar) = 0
          · have hgi := hdiff (D.g i) (z.1, ystar) (hStanding.2.2.2 i) c b
              (fun k => (T (ψ k))⁻¹) (0, ε • w) hc hb hscaled
            have hneg : fderiv ℝ (D.g i) (z.1, ystar) (0, ε • w) < 0 := by
              have hwi := hw i hi
              have he : ((0 : E n), ε • w) = ε • ((0 : E n), w) := by simp
              rw [he, map_smul, smul_eq_mul]
              exact mul_neg_of_pos_of_neg hε hwi
            filter_upwards [hgi.eventually (gt_mem_nhds hneg), hbgood] with k hk hbk
            have hdif : D.g i (c k) - D.g i (b k) < 0 :=
              (neg_of_mul_neg_right hk (le_of_lt (inv_pos.mpr (hTpos _))))
            exact le_of_lt (by linarith [hbk.1 i])
          · have hneg : D.g i (z.1, ystar) < 0 := lt_of_le_of_ne (hbfeas i) hi
            exact ((hStanding.2.2.2 i).continuous.continuousAt.tendsto.comp hc).eventually
              (gt_mem_nhds hneg) |>.mono fun k hk => hk.le
        have hfc := hdiff D.f (z.1, ystar) hStanding.2.1 c b
          (fun k => (T (ψ k))⁻¹) (0, ε • w) hc hb hscaled
        have hfc' : Tendsto (fun k => (T (ψ k))⁻¹ * (D.f (c k) - D.f (b k))) atTop
            (𝓝 (ε * L)) := by
          have he : ((0 : E n), ε • w) = ε • ((0 : E n), w) := by simp
          rw [he, map_smul, smul_eq_mul] at hfc
          exact hfc
        have hfx := (hdir D.f hStanding.2.1).comp hψt
        have hdiffineq : ∀ᶠ k in atTop,
            (T (ψ k))⁻¹ * (D.f (X (ψ k)) - D.f z) <
              r + (T (ψ k))⁻¹ * (D.f (c k) - D.f (b k)) := by
          filter_upwards [hcfeas, hbgood] with k hck hbk
          have hopt : D.f (X (ψ k)) ≤ D.f (c k) := (ha (φ (ψ k))).1.2.2 (c k).2 hck
          have hless := hbk.2
          have hmul : (T (ψ k))⁻¹ * (D.f (b k) - D.f z) < r := by
            rw [inv_mul_eq_div]
            apply (div_lt_iff₀ (hTpos (ψ k))).mpr
            nlinarith
          nlinarith [inv_pos.mpr (hTpos (ψ k))]
        have hlimineq : fderiv ℝ D.f z d ≤ r + ε * L :=
          le_of_tendsto_of_tendsto hfx (tendsto_const_nhds.add hfc') (hdiffineq.mono fun k hk => hk.le)
        exact (not_le_of_gt hεL) hlimineq
      have hz := hexclude d ⟨hF, hG, EReal.sub_nonpos.mpr hval, hg⟩
      simp [hz] at hdnorm
