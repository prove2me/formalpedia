-- Prove2me | solution 1 for DirKKTBilevel.VP.Supplement.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:43.807976+00:00
-- url     : https://prove2.me/submissions/faa80658-3b63-4999-b996-571ac2c15bf3

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

open DirKKTBilevel
open DirKKTBilevel.VP
open DirKKTBilevel.VP.Supplement

/-- Lemma 4.1, p. 15: let `ȳ ∈ 𝓕(x̄)`. If either `𝓕` satisfies RS at `(x̄, ȳ)` in direction `u`, or
`D₊𝓕(x̄, ȳ; u) ≠ ∅` and `𝓕` is RCR-regular at `(x̄, ȳ)`, then `D₊𝓕(x̄, ȳ; u) = L(x̄, ȳ; u)`. -/
theorem solution {n m p : ℕ} (g : Z n m → E p) (hg : ContDiff ℝ 1 g)
    (x : E n) (y : E m) (u : E n) (hy : y ∈ feasLL g x)
    (h : IsRSDir g x y u ∨ ((diniFeas g x y u).Nonempty ∧ IsRCR g x y)) :
    diniFeas g x y u = linLL g x y u := by
      focus
        haveI instCS : ContinuousSMul ℝ (Z n m) := IsBoundedSMul.continuousSMul
        have hdiff : ∀ i, Differentiable ℝ (fun z => g z i) := by
          intro i
          have := hg.differentiable (by norm_num)
          fun_prop
        have hcg : ∀ i, Continuous (fun z => g z i) := by
          intro i
          have := hg.continuous
          fun_prop
        have hci : ∀ v : E m, Continuous fun t : ℝ => (WithLp.toLp 2 (x + t • u, y + t • v) : Z n m) := by
          intro v; fun_prop
        have heq : ∀ (a b : E n) (c d : E m),
            (WithLp.toLp 2 (a, c) : Z n m) + WithLp.toLp 2 (b, d) = WithLp.toLp 2 (a + b, c + d) := by
          intro a b c d; rfl
        have heqs : ∀ (t : ℝ) (b : E n) (d : E m),
            t • (WithLp.toLp 2 (b, d) : Z n m) = WithLp.toLp 2 (t • b, t • d) := by
          intro t b d; rfl
        have hlim : ∀ i (w : Z n m) (R : ℝ → Z n m),
            Tendsto (fun t => t⁻¹ • R t) (𝓝[>] 0) (𝓝 0) →
            Tendsto (fun t : ℝ => t⁻¹ • (g (WithLp.toLp 2 (x, y) + (t • w + R t)) i
              - g (WithLp.toLp 2 (x, y)) i)) (𝓝[>] 0)
              (𝓝 (fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) w)) := by
          intro i w R hR
          have hd := ((hdiff i) (WithLp.toLp 2 (x, y))).hasFDerivAt.hasFDerivWithinAt
            (s := Set.univ)
          have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≠ 0 :=
            eventually_mem_nhdsWithin.mono (fun t ht => ne_of_gt ht)
          have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
          have hA : Tendsto (fun t : ℝ => t • w + R t) (𝓝[>] 0) (𝓝 0) := by
            have h1 := (ht.smul_const w).add (ht.smul hR)
            rw [zero_smul, zero_smul, add_zero] at h1
            refine h1.congr' (hev.mono fun t ht => ?_)
            rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
          have hB : Tendsto (fun t : ℝ => t⁻¹ • (t • w + R t)) (𝓝[>] 0) (𝓝 w) := by
            have h1 : Tendsto (fun t : ℝ => w + t⁻¹ • R t) (𝓝[>] 0) (𝓝 w) := by
              simpa using (tendsto_const_nhds (x := w)).add hR
            refine h1.congr' (hev.mono fun t ht => ?_)
            simp [smul_add, smul_smul, ht]
          set z0 : Z n m := WithLp.toLp 2 (x, y)
          set D := fderiv ℝ (fun z => g z i) z0
          have hlo := ((hdiff i) z0).hasFDerivAt.isLittleO
          have h2 := hlo.comp_tendsto (show Tendsto (fun t : ℝ => z0 + (t • w + R t)) (𝓝[>] 0) (𝓝 z0) by
            simpa using (tendsto_const_nhds (x := z0)).add hA)
          have hbd : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖t • w + R t‖ ≤ (‖w‖ + 1) * ‖t‖ := by
            have h3 : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖t⁻¹ • (t • w + R t)‖ < ‖w‖ + 1 :=
              (hB.norm).eventually (gt_mem_nhds (by linarith))
            filter_upwards [h3, eventually_mem_nhdsWithin] with t h3 ht
            have ht' : (0:ℝ) < t := ht
            rw [norm_smul, norm_inv] at h3
            have hnt : 0 < ‖t‖ := norm_pos_iff.2 ht'.ne'
            rw [inv_mul_lt_iff₀ hnt] at h3
            linarith
          have hO : (fun t : ℝ => t • w + R t) =O[𝓝[>] 0] (fun t : ℝ => t) :=
            Asymptotics.IsBigO.of_bound _ hbd
          have h4 : (fun t : ℝ => g (z0 + (t • w + R t)) i - g z0 i - D (t • w + R t)) =o[𝓝[>] 0]
              (fun t : ℝ => t) := by
            have := h2.trans_isBigO (show (fun t : ℝ => z0 + (t • w + R t) - z0) =O[𝓝[>] 0] (fun t : ℝ => t) by
              simp only [add_sub_cancel_left]; exact hO)
            refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
            simp only [Function.comp_apply, add_sub_cancel_left]
            rfl
          have h5 := h4.tendsto_div_nhds_zero
          have h6 : Tendsto (fun t : ℝ => D (t⁻¹ • (t • w + R t))) (𝓝[>] 0) (𝓝 (D w)) :=
            (D.continuous.tendsto w).comp hB
          have h7 := h6.add h5
          rw [add_zero] at h7
          refine h7.congr' (hev.mono fun t ht => ?_)
          simp only [map_smul, smul_eq_mul]
          field_simp
          ring
        have hc0 : Continuous fun e : E m => (WithLp.toLp 2 ((0:E n), e) : Z n m) := by fun_prop
        have hpos : ∀ t : ℝ, 0 < t → (WithLp.toLp 2 (x, y) : Z n m) + (t • WithLp.toLp 2 (u, 0) + 0) = 0 → True :=
          fun _ _ _ => trivial
        have hsub : diniFeas g x y u ⊆ linLL g x y u := by
          rintro v ⟨r, hr, hev⟩ i hi
          have hR : Tendsto (fun t : ℝ => t⁻¹ • (WithLp.toLp 2 ((0:E n), r t) : Z n m)) (𝓝[>] 0) (𝓝 0) := by
            have := (hc0.tendsto 0).comp hr
            simp only [Function.comp_def] at this
            have h00 : (WithLp.toLp 2 ((0:E n), (0:E m)) : Z n m) = 0 := rfl
            rw [h00] at this
            refine this.congr' (Eventually.of_forall fun t => ?_)
            show (WithLp.toLp 2 ((0:E n), t⁻¹ • r t) : Z n m) = t⁻¹ • WithLp.toLp 2 ((0:E n), r t)
            rw [heqs, smul_zero]
          have hL := hlim i (WithLp.toLp 2 (u, v)) _ hR
          refine le_of_tendsto hL ?_
          filter_upwards [hev, eventually_mem_nhdsWithin] with t ht htp
          have htp' : (0:ℝ) < t := htp
          have hpt : (WithLp.toLp 2 (x, y) : Z n m) + (t • WithLp.toLp 2 (u, v) + WithLp.toLp 2 ((0:E n), r t))
              = WithLp.toLp 2 (x + t • u, y + t • v + r t) := by
            rw [heqs, heq, heq, add_zero, add_assoc]
          rw [hpt, hi, sub_zero, smul_eq_mul]
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htp'.le) (ht i)
        refine Set.Subset.antisymm hsub ?_
        rcases h with hRS | ⟨hne, hRCR⟩
        · obtain ⟨-, κ, ε, δ, hκ, hε, hδ, hRS⟩ := hRS
          intro v hv
          set z0 : Z n m := WithLp.toLp 2 (x, y) with hz0
          set w : Z n m := WithLp.toLp 2 (u, v) with hw
          have hpt : ∀ t : ℝ, z0 + (t • w + 0) = WithLp.toLp 2 (x + t • u, y + t • v) := by
            intro t; rw [hz0, hw, heqs, heq, add_zero]
          have hpp : Tendsto (fun t : ℝ => t⁻¹ • posPart (g (WithLp.toLp 2 (x + t • u, y + t • v))))
              (𝓝[>] 0) (𝓝 0) := by
            have hc : Tendsto (fun t : ℝ => WithLp.toLp 2
                (fun j => t⁻¹ * max (g (WithLp.toLp 2 (x + t • u, y + t • v)) j) 0) : ℝ → E p)
                (𝓝[>] 0) (𝓝 (WithLp.toLp 2 (0 : Fin p → ℝ))) := by
              refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
              rw [tendsto_pi_nhds]
              intro j
              by_cases hj : g z0 j = 0
              · have hL := hlim j w (fun _ => 0) (by simp)
                simp only [hpt, hj, sub_zero, smul_eq_mul] at hL
                have hD : fderiv ℝ (fun z => g z j) z0 w ≤ 0 := hv j hj
                have hm := hL.max (tendsto_const_nhds (x := (0:ℝ)))
                rw [max_eq_right hD] at hm
                refine hm.congr' (eventually_mem_nhdsWithin.mono fun t ht => ?_)
                have ht' : (0:ℝ) < t := ht
                show _ = t⁻¹ * _
                rw [mul_max_of_nonneg _ _ (inv_nonneg.2 ht'.le), mul_zero]
              · have hneg : g z0 j < 0 := lt_of_le_of_ne (hy j) hj
                have hcont := ((hcg j).tendsto _).comp ((hci v).tendsto 0)
                have hev : ∀ᶠ t : ℝ in 𝓝 0, g (WithLp.toLp 2 (x + t • u, y + t • v)) j < 0 :=
                  hcont.eventually (gt_mem_nhds (by simpa using hneg))
                refine tendsto_const_nhds.congr' ((hev.filter_mono nhdsWithin_le_nhds).mono fun t ht => ?_)
                simp [max_eq_right ht.le]
            have h00 : (WithLp.toLp 2 (0 : Fin p → ℝ) : E p) = 0 := rfl
            rw [h00] at hc
            refine hc.congr' (Eventually.of_forall fun t => ?_)
            ext j
            simp [DirKKTBilevel.VP.posPart]
          have htu : Tendsto (fun t : ℝ => ‖t • u‖) (𝓝 0) (𝓝 0) := by
            have : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 ((0:ℝ) • u)) :=
              tendsto_id.smul_const u
            rw [zero_smul] at this
            simpa using this.norm
          have htv : Tendsto (fun t : ℝ => y + t • v) (𝓝 0) (𝓝 y) := by
            have : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0:ℝ) • v)) :=
              tendsto_id.smul_const v
            rw [zero_smul] at this
            simpa using (tendsto_const_nhds (x := y)).add this
          have hP : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ Metric.infEDist (y + t • v) (feasLL g (x + t • u)) ≤
              ENNReal.ofReal (κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖) := by
            have h1 : ∀ᶠ t in 𝓝 (0:ℝ), ‖t • u‖ < ε := htu.eventually (gt_mem_nhds hε)
            have h2 : ∀ᶠ t in 𝓝 (0:ℝ), y + t • v ∈ Metric.ball y ε := htv.eventually (Metric.ball_mem_nhds y hε)
            filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds,
              eventually_mem_nhdsWithin] with t h1 h2 ht
            have ht' : (0:ℝ) < t := ht
            refine ⟨ht', hRS _ ?_ _ h2⟩
            rw [add_sub_cancel_left]
            refine ⟨h1, ?_⟩
            rw [norm_smul, Real.norm_of_nonneg ht'.le, smul_smul, mul_comm, ← smul_smul, sub_self, norm_zero]
            positivity
          have hW : ∀ t : ℝ, ∃ W : E m, (0 < t ∧ Metric.infEDist (y + t • v) (feasLL g (x + t • u)) ≤
              ENNReal.ofReal (κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖)) →
              W ∈ feasLL g (x + t • u) ∧
              dist (y + t • v) W < κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖ + t ^ 2 := by
            intro t
            by_cases hPt : 0 < t ∧ Metric.infEDist (y + t • v) (feasLL g (x + t • u)) ≤
              ENNReal.ofReal (κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖)
            · have hlt : Metric.infEDist (y + t • v) (feasLL g (x + t • u)) <
                  ENNReal.ofReal (κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖ + t ^ 2) := by
                refine lt_of_le_of_lt hPt.2 ?_
                rw [ENNReal.ofReal_lt_ofReal_iff (by have := hPt.1; positivity)]
                have := hPt.1
                have : 0 < t ^ 2 := by positivity
                linarith
              obtain ⟨W, hWm, hWd⟩ := Metric.infEDist_lt_iff.1 hlt
              exact ⟨W, fun _ => ⟨hWm, edist_lt_ofReal.1 hWd⟩⟩
            · exact ⟨y, fun h' => absurd h' hPt⟩
          choose W hW using hW
          refine ⟨fun t => W t - (y + t • v), ?_, ?_⟩
          · have hbound : Tendsto (fun t : ℝ => κ * ‖t⁻¹ • posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖ + t)
                (𝓝[>] 0) (𝓝 0) := by
              have h1 := (hpp.norm.const_mul κ).add (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0)
                |> fun h => (tendsto_id.mono_left h))
              simpa using h1
            refine squeeze_zero_norm' ?_ hbound
            filter_upwards [hP] with t ht
            have hd := (hW t ht).2
            have ht' := ht.1
            rw [norm_smul, norm_smul, norm_inv, Real.norm_of_nonneg ht'.le, ← dist_eq_norm, dist_comm]
            rw [inv_mul_le_iff₀ ht']
            have : t * (κ * (t⁻¹ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖) + t)
                = κ * ‖posPart (g (WithLp.toLp 2 (x + t • u, y + t • v)))‖ + t ^ 2 := by
              field_simp
            rw [this]
            exact hd.le
          · filter_upwards [hP] with t ht
            have := (hW t ht).1
            simpa using this
        · obtain ⟨v0, hv0⟩ := hne
          have happrox : ∀ v : E m, (∀ ε > 0, ∀ᶠ t in 𝓝[>] (0:ℝ),
              ∃ y' ∈ feasLL g (x + t • u), ‖y + t • v - y'‖ ≤ ε * t) → v ∈ diniFeas g x y u := by
            intro v hv
            have hW : ∀ t : ℝ, ∃ W : E m, (0 < t ∧ (feasLL g (x + t • u)).Nonempty) →
                W ∈ feasLL g (x + t • u) ∧
                dist (y + t • v) W < Metric.infDist (y + t • v) (feasLL g (x + t • u)) + t ^ 2 := by
              intro t
              by_cases hPt : 0 < t ∧ (feasLL g (x + t • u)).Nonempty
              · obtain ⟨W, hWm, hWd⟩ := (Metric.infDist_lt_iff hPt.2).1
                  (show Metric.infDist (y + t • v) (feasLL g (x + t • u)) <
                    Metric.infDist (y + t • v) (feasLL g (x + t • u)) + t ^ 2 by
                      have := hPt.1; have : 0 < t ^ 2 := by positivity
                      linarith)
                exact ⟨W, fun _ => ⟨hWm, hWd⟩⟩
              · exact ⟨y, fun h' => absurd h' hPt⟩
            choose W hW using hW
            refine ⟨fun t => W t - (y + t • v), ?_, ?_⟩
            · rw [Metric.tendsto_nhds]
              intro ε hε
              have h1 := hv (ε / 2) (by positivity)
              have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < ε / 2 :=
                (nhdsWithin_le_nhds (s := Set.Ioi 0)) (gt_mem_nhds (by positivity))
              filter_upwards [h1, h2, eventually_mem_nhdsWithin] with t h1 h2 ht
              have ht' : (0:ℝ) < t := ht
              obtain ⟨y', hy', hd⟩ := h1
              have hWt := hW t ⟨ht', y', hy'⟩
              have hid : Metric.infDist (y + t • v) (feasLL g (x + t • u)) ≤ ε / 2 * t := by
                refine (Metric.infDist_le_dist_of_mem hy').trans ?_
                rw [dist_eq_norm]; exact hd
              rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg ht'.le, ← dist_eq_norm,
                dist_comm, inv_mul_lt_iff₀ ht']
              have : t ^ 2 < ε / 2 * t := by nlinarith
              linarith [hWt.2]
            · filter_upwards [hv 1 one_pos, eventually_mem_nhdsWithin] with t h1 ht
              obtain ⟨y'', hy'', -⟩ := h1
              have := (hW t ⟨ht, y'', hy''⟩).1
              simpa using this
          have hkey : ∀ v ∈ linLL g x y u, ∀ l : ℝ, 0 < l → l ≤ 1 →
              (1 - l) • v + l • v0 ∈ diniFeas g x y u := by
            have hcore : ∀ (J : Set (Fin p)) (w : E m), J ⊆ activeLL g x y →
                (∀ j ∈ J, fderiv ℝ (fun z => g z j) (WithLp.toLp 2 (x, y))
                  (WithLp.toLp 2 ((0 : E n), w)) = 0) →
                ∀ y0 : ℝ → E m, Tendsto (fun t => t⁻¹ • (y0 t - y)) (𝓝[>] 0) (𝓝 v0) →
                ∃ c : ℝ → E m, Tendsto (fun t => t⁻¹ • c t) (𝓝[>] 0) (𝓝 0) ∧
                  ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ j ∈ J,
                    g (WithLp.toLp 2 (x + t • u, y0 t + t • w + c t)) j ≤
                      g (WithLp.toLp 2 (x + t • u, y0 t)) j := by
              intro J w hJ hJw y0 hy0
              clear * - hg hRCR hJ hJw hy0
              classical
              obtain ⟨-, δ, hδ, hRk⟩ := hRCR
              set z0 : Z n m := WithLp.toLp 2 (x, y) with hz0
              set D : Fin p → Z n m → E m := fun j z => gradY (fun w => g w j) z with hDdef
              have hgk : ∀ k, ContDiff ℝ 1 (fun z => g z k) := by
                intro k
                exact (PiLp.proj 2 (fun _ : Fin p => ℝ) k).contDiff.comp hg
              have hD : ∀ j z d, inner ℝ (D j z) d =
                  fderiv ℝ (fun w => g w j) z (WithLp.toLp 2 ((0:E n), d)) := by
                intro j z d
                have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Z n m)
                  (x := WithLp.toLp 2 ((0:E n), d)) (y := fderiv ℝ (fun w => g w j) z)
                rw [WithLp.prod_inner_apply] at h1
                simp only [inner_zero_right, zero_add] at h1
                rw [← h1]
                rfl
              obtain ⟨B, hBJ, -, hBspan, hBli⟩ := exists_linearIndepOn_extension (K := ℝ)
                (v := fun j => D j z0) (linearIndepOn_empty ℝ _) (Set.empty_subset J)
              have hdual : ∃ e : Fin p → E m, (∀ k, k ∉ B → e k = 0) ∧
                  ∀ k ∈ B, ∀ l ∈ B, inner ℝ (D l z0) (e k) = if l = k then 1 else 0 := by
                have hli : LinearIndependent ℝ (fun i : B => D i z0) := hBli
                set V := Submodule.span ℝ (Set.range (fun i : B => D i z0)) with hV
                obtain ⟨b, hb⟩ : ∃ b : Module.Basis B ℝ V, b = Module.Basis.span hli := ⟨_, rfl⟩
                haveI instFD : FiniteDimensional ℝ V := FiniteDimensional.finiteDimensional_submodule V
                haveI instCV : CompleteSpace V := FiniteDimensional.complete ℝ V
                refine ⟨fun k => if hk : k ∈ B then
                  (((InnerProductSpace.toDual ℝ V).symm (LinearMap.toContinuousLinearMap (b.coord ⟨k, hk⟩)) : V) : E m)
                  else 0, fun k hk => by simp [hk], ?_⟩
                intro k hk l hl
                simp only [hk, dite_true]
                rw [real_inner_comm]
                have hmem : D l z0 ∈ V := Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
                have h2 : (⟨D l z0, hmem⟩ : V) = b ⟨l, hl⟩ := by
                  rw [hb, Module.Basis.span_apply]
                have h3 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V)
                  (x := ⟨D l z0, hmem⟩) (y := (LinearMap.toContinuousLinearMap (b.coord ⟨k, hk⟩)))
                rw [Submodule.coe_inner] at h3
                simp only at h3
                rw [h3, h2]
                simp [Module.Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff, eq_comm]
              obtain ⟨e, he0, he⟩ := hdual
              have hspan : ∀ ζ ∈ Metric.ball z0 δ, ∀ j ∈ J, ∃ μ : Fin p → ℝ, (∀ k, k ∉ B → μ k = 0) ∧
                  ∀ d : E m, fderiv ℝ (fun w => g w j) ζ (WithLp.toLp 2 ((0:E n), d)) =
                    ∑ k, μ k * fderiv ℝ (fun w => g w k) ζ (WithLp.toLp 2 ((0:E n), d)) := by
                intro ζ hζ j hj
                have hB' : B ⊆ activeLL g x y := hBJ.trans hJ
                have hspan0 : Submodule.span ℝ ((fun j => D j z0) '' B) =
                    Submodule.span ℝ ((fun j => D j z0) '' J) := by
                  apply le_antisymm (Submodule.span_mono (Set.image_mono hBJ))
                  rw [Submodule.span_le]; exact hBspan
                have hle : Submodule.span ℝ ((fun j => D j ζ) '' B) ≤
                    Submodule.span ℝ ((fun j => D j ζ) '' J) :=
                  Submodule.span_mono (Set.image_mono hBJ)
                have h1 : Module.finrank ℝ (Submodule.span ℝ ((fun j => D j ζ) '' B)) =
                    Module.finrank ℝ (Submodule.span ℝ ((fun j => D j z0) '' B)) := hRk B hB' ζ hζ
                have h2 : Module.finrank ℝ (Submodule.span ℝ ((fun j => D j ζ) '' J)) =
                    Module.finrank ℝ (Submodule.span ℝ ((fun j => D j z0) '' J)) := hRk J hJ ζ hζ
                have heq : Submodule.span ℝ ((fun j => D j ζ) '' B) =
                    Submodule.span ℝ ((fun j => D j ζ) '' J) := by
                  apply Submodule.eq_of_le_of_finrank_eq hle
                  rw [h1, h2, hspan0]
                have hmem : D j ζ ∈ Submodule.span ℝ ((fun j => D j ζ) '' B) := by
                  rw [heq]; exact Submodule.subset_span ⟨j, hj, rfl⟩
                rw [Finsupp.mem_span_image_iff_linearCombination] at hmem
                obtain ⟨l, hl, hsum⟩ := hmem
                refine ⟨fun k => l k, fun k hk => ?_, fun d => ?_⟩
                · by_contra h; exact hk (hl (Finsupp.mem_support_iff.2 h))
                · rw [← hD, ← hsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
                  · simp_rw [sum_inner, real_inner_smul_left, hD]
                  · simp
              set Φ : Z n m → Z n m := fun z => z + WithLp.toLp 2 ((0:E n),
                ∑ k, (g z k - inner ℝ (D k z0) (WithLp.ofLp z).2) • e k) with hΦdef
              obtain ⟨Φ', hΦ, hΦ'0⟩ : ∃ Φ' : Z n m ≃L[ℝ] Z n m,
                  HasStrictFDerivAt Φ (Φ' : Z n m →L[ℝ] Z n m) z0 ∧
                  ∀ d : E m, Φ'.symm (WithLp.toLp 2 ((0:E n), d)) = WithLp.toLp 2 ((0:E n), d) := by
                let T : E m →L[ℝ] Z n m :=
                  (WithLp.prodContinuousLinearEquiv 2 ℝ (E n) (E m)).symm.toContinuousLinearMap.comp
                    (ContinuousLinearMap.inr ℝ (E n) (E m))
                let P2 : Z n m →L[ℝ] E m := WithLp.sndL 2 ℝ (E n) (E m)
                have hT : ∀ d, T d = WithLp.toLp 2 ((0:E n), d) := fun d => rfl
                have hP2 : ∀ z, P2 z = (WithLp.ofLp z).2 := fun z => rfl
                let S' : Z n m →L[ℝ] E m := ∑ k, (fderiv ℝ (fun w => g w k) z0 -
                  (innerSL ℝ (D k z0)).comp P2).smulRight (e k)
                have hS : HasStrictFDerivAt (fun z => ∑ k, (g z k - inner ℝ (D k z0) (WithLp.ofLp z).2) • e k)
                    S' z0 := by
                  have := HasStrictFDerivAt.fun_sum (u := Finset.univ) (x := z0) (fun k _ =>
                    (((hgk k).contDiffAt.hasStrictFDerivAt (by norm_num)).sub
                      ((innerSL ℝ (D k z0)).comp P2).hasStrictFDerivAt).smul_const (e k))
                  exact this
                have hST : ∀ s, S' (T s) = 0 := by
                  intro s
                  simp only [S', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
                    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hT, hP2]
                  refine Finset.sum_eq_zero fun k _ => ?_
                  rw [hD]; simp
                let F : Z n m →L[ℝ] Z n m := ContinuousLinearMap.id ℝ _ + T.comp S'
                let G : Z n m →L[ℝ] Z n m := ContinuousLinearMap.id ℝ _ - T.comp S'
                have hFG : Function.LeftInverse G F := by
                  intro a
                  simp only [F, G, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
                    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add, hST, map_zero,
                    add_zero, add_sub_cancel_right]
                  abel
                have hGF : Function.RightInverse G F := by
                  intro a
                  simp only [F, G, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
                    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub, hST, map_zero,
                    sub_zero, sub_add_cancel]
                  abel
                refine ⟨ContinuousLinearEquiv.equivOfInverse F G hFG hGF, ?_, ?_⟩
                · have := (hasStrictFDerivAt_id z0).add (T.hasStrictFDerivAt.comp z0 hS)
                  exact this
                · intro d
                  show G (T d) = T d
                  simp only [G, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                    ContinuousLinearMap.comp_apply, hST, map_zero, sub_zero]
              have hΦ1 : ∀ z, (WithLp.ofLp (Φ z)).1 = (WithLp.ofLp z).1 := by
                intro z; simp [hΦdef]
              have hΦ2 : ∀ z, ∀ l ∈ B, inner ℝ (D l z0) (WithLp.ofLp (Φ z)).2 = g z l := by
                intro z l hl
                simp only [hΦdef, WithLp.ofLp_add, Prod.snd_add, inner_add_right, inner_sum, inner_smul_right]
                rw [Finset.sum_eq_single l]
                · rw [he l hl l hl]; simp
                · intro k _ hkl
                  by_cases hk : k ∈ B
                  · rw [he k hk l hl, if_neg (Ne.symm hkl)]; simp
                  · rw [he0 k hk]; simp
                · simp
              have hwB : ∀ l ∈ B, inner ℝ (D l z0) w = 0 := fun l hl => by rw [hD]; exact hJw l (hBJ hl)
              have hN : ∀ d : E m, ‖(WithLp.toLp 2 ((0:E n), d) : Z n m)‖ = ‖d‖ := by
                intro d
                rw [WithLp.prod_norm_eq_of_L2]
                simp [Real.sqrt_sq (norm_nonneg d)]
              have hsnd : ∀ a b : Z n m, (WithLp.ofLp a).1 = (WithLp.ofLp b).1 →
                  a - b = WithLp.toLp 2 ((0:E n), (WithLp.ofLp a).2 - (WithLp.ofLp b).2) := by
                intro a b hab
                rw [WithLp.ext_iff, WithLp.ofLp_sub, WithLp.ofLp_toLp]
                refine Prod.ext ?_ ?_
                · simp only [Prod.fst_sub, hab, sub_self]
                · simp only [Prod.snd_sub]
              haveI : ContinuousSMul ℝ (Z n m) := IsBoundedSMul.continuousSMul
              set F := hΦ.localInverse Φ Φ' z0 with hFdef
              have hFd := hΦ.to_localInverse
              have hRI := hΦ.eventually_right_inverse
              have hLI := hΦ.eventually_left_inverse
              obtain ⟨K, U, hU, hLip⟩ := hFd.exists_lipschitzOnWith
              have hFt := hΦ.localInverse_tendsto
              have hgood : U ∩ {q | Φ (F q) = q} ∩ F ⁻¹' Metric.ball z0 δ ∈ 𝓝 (Φ z0) :=
                inter_mem (inter_mem hU hRI) (tendsto_def.1 hFt _ (Metric.ball_mem_nhds z0 hδ))
              obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hgood
              have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
              have hy0' : Tendsto y0 (𝓝[>] 0) (𝓝 y) := by
                have := (ht0.smul hy0).add (tendsto_const_nhds (x := y))
                rw [zero_smul, zero_add] at this
                refine this.congr' (eventually_mem_nhdsWithin.mono fun t ht => ?_)
                have ht' : t ≠ 0 := ne_of_gt ht
                simp [smul_smul, mul_inv_cancel₀ ht']
              set zt : ℝ → Z n m := fun t => WithLp.toLp 2 (x + t • u, y0 t) with hzt
              have hzt0 : Tendsto zt (𝓝[>] 0) (𝓝 z0) := by
                have hx : Tendsto (fun t : ℝ => x + t • u) (𝓝[>] 0) (𝓝 x) := by
                  have := (tendsto_const_nhds (x := x)).add (ht0.smul_const u)
                  simpa using this
                have hc : Continuous fun q : E n × E m => (WithLp.toLp 2 q : Z n m) := by fun_prop
                exact (hc.tendsto (x, y)).comp (hx.prodMk_nhds hy0')
              have hΦzt : Tendsto (fun t => Φ (zt t)) (𝓝[>] 0) (𝓝 (Φ z0)) :=
                hΦ.continuousAt.tendsto.comp hzt0
              set q : ℝ → ℝ → Z n m := fun t s => Φ (zt t) + WithLp.toLp 2 ((0:E n), (s * t) • w) with hq
              set ζ : ℝ → ℝ → Z n m := fun t s => F (q t s) with hζ
              set c : ℝ → E m := fun t => (WithLp.ofLp (ζ t 1)).2 - y0 t - t • w with hc
              have hwt : Tendsto (fun t : ℝ => t * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
                simpa using ht0.mul_const ‖w‖
              have hE : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ F (Φ (zt t)) = zt t ∧
                  dist (Φ (zt t)) (Φ z0) < ρ / 2 ∧ t * ‖w‖ < ρ / 2 := by
                filter_upwards [eventually_mem_nhdsWithin, hzt0.eventually hLI,
                  hΦzt.eventually (Metric.ball_mem_nhds _ (half_pos hρ)),
                  hwt.eventually (gt_mem_nhds (half_pos hρ))] with t h1 h2 h3 h4
                exact ⟨h1, h2, h3, h4⟩
              have hmain : ∀ t, (0 < t ∧ F (Φ (zt t)) = zt t ∧
                  dist (Φ (zt t)) (Φ z0) < ρ / 2 ∧ t * ‖w‖ < ρ / 2) →
                  (∀ j ∈ J, g (WithLp.toLp 2 (x + t • u, y0 t + t • w + c t)) j = g (zt t) j) ∧
                  F (q t 1) - F (q t 0) - WithLp.toLp 2 ((0:E n), t • w) = WithLp.toLp 2 ((0:E n), c t) := by
                rintro t ⟨ht, hlt, hd, htw⟩
                have hqd : ∀ s s', dist (q t s) (q t s') = |s - s'| * (t * ‖w‖) := by
                  intro s s'
                  rw [dist_eq_norm]
                  have : q t s - q t s' = WithLp.toLp 2 ((0:E n), ((s - s') * t) • w) := by
                    simp only [hq]
                    rw [WithLp.ext_iff]; ext <;> simp [sub_smul, sub_mul]
                  rw [this, hN, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos ht]; ring
                have hqb : ∀ s ∈ Set.Icc (0:ℝ) 1, q t s ∈ Metric.ball (Φ z0) ρ := by
                  intro s hs
                  rw [Metric.mem_ball]
                  have h1 : dist (q t s) (Φ (zt t)) ≤ t * ‖w‖ := by
                    have := hqd s 0
                    have h0 : q t 0 = Φ (zt t) := by simp [hq]
                    rw [h0] at this
                    rw [this, sub_zero, abs_of_nonneg hs.1]
                    exact mul_le_of_le_one_left (mul_nonneg ht.le (norm_nonneg w)) hs.2
                  exact lt_of_le_of_lt (dist_triangle (q t s) (Φ (zt t)) (Φ z0)) (by linarith only [h1, hd, htw])
                have hgd : ∀ s ∈ Set.Icc (0:ℝ) 1, q t s ∈ U ∧ Φ (ζ t s) = q t s ∧ ζ t s ∈ Metric.ball z0 δ := by
                  intro s hs
                  have h := hball (hqb s hs)
                  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq] at h
                  exact ⟨h.1.1, h.1.2, h.2⟩
                have hq0 : q t 0 = Φ (zt t) := by simp [hq]
                have hζ0 : ζ t 0 = zt t := by simp only [hζ]; rw [hq0, hlt]
                have hfst : ∀ s ∈ Set.Icc (0:ℝ) 1, (WithLp.ofLp (ζ t s)).1 = x + t • u := by
                  intro s hs
                  rw [← hΦ1, (hgd s hs).2.1]
                  simp only [hq, WithLp.ofLp_add, Prod.fst_add, hΦ1]
                  simp [hzt]
                have hgB : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ l ∈ B, g (ζ t s) l = g (zt t) l := by
                  intro s hs l hl
                  rw [← hΦ2 _ l hl, (hgd s hs).2.1, ← hΦ2 (zt t) l hl]
                  simp only [hq, WithLp.ofLp_add, Prod.snd_add, inner_add_right, inner_smul_right, hwB l hl]
                  simp
                have hLipt : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ s' ∈ Set.Icc (0:ℝ) 1,
                    dist (ζ t s') (ζ t s) ≤ K * (t * ‖w‖) * |s' - s| := by
                  intro s hs s' hs'
                  have := hLip.dist_le_mul _ (hgd s' hs').1 _ (hgd s hs).1
                  rw [hqd] at this
                  simp only [hζ]
                  linarith
                have hconst : ∀ j ∈ J, g (ζ t 1) j = g (ζ t 0) j := by
                  intro j hj
                  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1,
                      HasDerivWithinAt (fun s => g (ζ t s) j) 0 (Set.Icc 0 1) s := by
                    intro s hs
                    set ζs := ζ t s with hζs
                    obtain ⟨μ, hμ0, hμ⟩ := hspan ζs (hgd s hs).2.2 j hj
                    have hoj := ((hgk j).differentiable (by norm_num) ζs).hasFDerivAt.isLittleO
                    have hok : ∀ k, (fun z => g z k - g ζs k - fderiv ℝ (fun w => g w k) ζs (z - ζs)) =o[𝓝 ζs]
                        (fun z => z - ζs) := fun k => ((hgk k).differentiable (by norm_num) ζs).hasFDerivAt.isLittleO
                    have hR := hoj.sub (Asymptotics.IsLittleO.sum (s := Finset.univ)
                      (fun k _ => (hok k).const_mul_left (μ k)))
                    have hζt : Tendsto (ζ t) (𝓝[Set.Icc 0 1] s) (𝓝 ζs) := by
                      rw [tendsto_iff_dist_tendsto_zero]
                      have h0 : Tendsto (fun s' : ℝ => K * (t * ‖w‖) * |s' - s|) (𝓝[Set.Icc 0 1] s) (𝓝 0) := by
                        have : Tendsto (fun s' : ℝ => K * (t * ‖w‖) * |s' - s|) (𝓝 s)
                            (𝓝 (K * (t * ‖w‖) * |s - s|)) :=
                          (continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).tendsto s
                        rw [sub_self, abs_zero, mul_zero] at this
                        exact this.mono_left nhdsWithin_le_nhds
                      refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ h0
                      filter_upwards [eventually_mem_nhdsWithin] with s' h2
                      exact hLipt s hs s' h2
                    have hR2 := hR.comp_tendsto hζt
                    have hO : (fun s' => ζ t s' - ζs) =O[𝓝[Set.Icc 0 1] s] (fun s' : ℝ => s' - s) := by
                      refine Asymptotics.IsBigO.of_bound (K * (t * ‖w‖)) ?_
                      filter_upwards [eventually_mem_nhdsWithin] with s' h2
                      rw [← dist_eq_norm, Real.norm_eq_abs]
                      exact hLipt s hs s' h2
                    have hR3 := hR2.trans_isBigO hO
                    rw [hasDerivWithinAt_iff_isLittleO]
                    refine hR3.congr' ?_ (Eventually.of_forall fun _ => rfl)
                    filter_upwards [eventually_mem_nhdsWithin] with s' h2
                    simp only [Function.comp_def, smul_zero, sub_zero, Finset.sum_apply]
                    have hdz := hsnd (ζ t s') ζs (by rw [hfst s' h2, hζs, hfst s hs])
                    rw [hdz, hμ]
                    have hsum : ∑ k, μ k * (g (ζ t s') k - g ζs k -
                        fderiv ℝ (fun w => g w k) ζs (WithLp.toLp 2 ((0:E n),
                          (WithLp.ofLp (ζ t s')).2 - (WithLp.ofLp ζs).2))) =
                        - ∑ k, μ k * fderiv ℝ (fun w => g w k) ζs (WithLp.toLp 2 ((0:E n),
                          (WithLp.ofLp (ζ t s')).2 - (WithLp.ofLp ζs).2)) := by
                      rw [← Finset.sum_neg_distrib]
                      refine Finset.sum_congr rfl fun k _ => ?_
                      by_cases hk : k ∈ B
                      · rw [hgB s' h2 k hk, hζs, hgB s hs k hk]; ring
                      · rw [hμ0 k hk]; ring
                    rw [hsum, ← hζs]; ring
                  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0:ℝ)) (C := 0)
                    hderiv (fun _ _ => by simp) (convex_Icc 0 1) (x := 0) (y := 1)
                    ⟨le_refl _, zero_le_one⟩ ⟨zero_le_one, le_refl _⟩
                  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
                  exact this
                have h1mem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl _⟩
                have hpt : WithLp.toLp 2 (x + t • u, y0 t + t • w + c t) = ζ t 1 := by
                  have h1 := hfst 1 h1mem
                  have h2 : y0 t + t • w + c t = (WithLp.ofLp (ζ t 1)).2 := by simp only [hc]; abel
                  rw [WithLp.ext_iff, WithLp.ofLp_toLp, h2, ← h1]
                refine ⟨fun j hj => ?_, ?_⟩
                · rw [hpt, hconst j hj, hζ0]
                · have h1 : F (q t 1) = ζ t 1 := rfl
                  have h0 : F (q t 0) = zt t := hζ0
                  rw [h1, h0, hsnd (ζ t 1) (zt t) ((hfst 1 h1mem).trans rfl)]
                  rw [WithLp.ext_iff, WithLp.ofLp_sub, WithLp.ofLp_toLp, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
                  refine Prod.ext ?_ ?_
                  · simp
                  · simp only [Prod.snd_sub, hc, hzt]; abel
              refine ⟨c, ?_, ?_⟩
              · have hfl := (hasStrictFDerivAt_iff_isLittleO.1 hFd)
                have hq1 : Tendsto (fun t => (q t 1, q t 0)) (𝓝[>] 0) (𝓝 (Φ z0, Φ z0)) := by
                  have hw0 : Tendsto (fun t : ℝ => (WithLp.toLp 2 ((0:E n), t • w) : Z n m)) (𝓝[>] 0) (𝓝 0) := by
                    rw [tendsto_zero_iff_norm_tendsto_zero]
                    simp only [hN, norm_smul, Real.norm_eq_abs]
                    have := (ht0.abs).mul_const ‖w‖
                    simpa using this
                  refine Tendsto.prodMk_nhds ?_ ?_
                  · have := hΦzt.add hw0
                    rw [add_zero] at this
                    simpa [hq] using this
                  · have h00 : (WithLp.toLp 2 ((0:E n), (0:E m)) : Z n m) = 0 := rfl
                    simpa [hq, h00] using hΦzt
                have h2 := hfl.comp_tendsto hq1
                have hO : (fun t => (q t 1, q t 0).1 - (q t 1, q t 0).2) =O[𝓝[>] 0] (fun t : ℝ => t) := by
                  refine Asymptotics.IsBigO.of_bound ‖w‖ (Eventually.of_forall fun t => ?_)
                  have : q t 1 - q t 0 = WithLp.toLp 2 ((0:E n), t • w) := by
                    simp only [hq]; rw [WithLp.ext_iff]; ext <;> simp
                  simp only [this, hN, norm_smul, Real.norm_eq_abs]
                  rw [mul_comm]
                have h3 := h2.trans_isBigO hO
                have h4 : (fun t => WithLp.toLp 2 ((0:E n), c t)) =o[𝓝[>] 0] (fun t : ℝ => t) := by
                  refine h3.congr' ?_ (Eventually.of_forall fun _ => rfl)
                  filter_upwards [hE] with t ht
                  simp only [Function.comp_def]
                  rw [← (hmain t ht).2, ContinuousLinearEquiv.coe_coe]
                  have : q t 1 - q t 0 = WithLp.toLp 2 ((0:E n), t • w) := by
                    simp only [hq]; rw [WithLp.ext_iff]; ext <;> simp
                  rw [this, hΦ'0]
                have h5 : c =o[𝓝[>] 0] (fun t : ℝ => t) := by
                  have := Asymptotics.isLittleO_norm_left.2 h4
                  simp only [hN] at this
                  exact Asymptotics.isLittleO_norm_left.1 this
                exact h5.tendsto_inv_smul_nhds_zero
              · filter_upwards [hE] with t ht j hj
                exact ((hmain t ht).1 j hj).le
            intro v hv l hl0 hl1
            obtain ⟨r0, hr0, hev0⟩ := id hv0
            set z0 : Z n m := WithLp.toLp 2 (x, y) with hz0
            set vl : E m := (1 - l) • v + l • v0 with hvl
            set w : E m := vl - v0 with hw
            have hlin : ∀ j, fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, vl)) =
                (1 - l) * fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, v)) +
                l * fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, v0)) := by
              intro j
              have : (WithLp.toLp 2 (u, vl) : Z n m) =
                  (1 - l) • WithLp.toLp 2 (u, v) + l • WithLp.toLp 2 (u, v0) := by
                rw [heqs, heqs, heq, ← add_smul]; simp [hvl]
              rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
            have hlin2 : ∀ j, fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 ((0 : E n), w)) =
                fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, vl)) -
                fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, v0)) := by
              intro j
              have : (WithLp.toLp 2 ((0 : E n), w) : Z n m) =
                  WithLp.toLp 2 (u, vl) - WithLp.toLp 2 (u, v0) := by
                rw [hw]
                show _ = WithLp.toLp 2 ((u, vl) - (u, v0))
                simp
              rw [this, map_sub]
            have hb : ∀ j, g z0 j = 0 → fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, v0)) ≤ 0 :=
              fun j hj => hsub hv0 j hj
            have hvle : ∀ j, g z0 j = 0 → fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, vl)) ≤ 0 := by
              intro j hj
              rw [hlin]
              have h1 := hv j hj
              have h2 := hb j hj
              exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl1) h1)
                (mul_nonpos_of_nonneg_of_nonpos hl0.le h2)
            set J : Set (Fin p) := {j | g z0 j = 0 ∧ fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, vl)) = 0}
            have hJ : J ⊆ activeLL g x y := fun j hj => hj.1
            have hJw : ∀ j ∈ J, fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 ((0 : E n), w)) = 0 := by
              intro j hj
              rw [hlin2, hj.2]
              have h0 := hj.2
              rw [hlin] at h0
              have h1 := hv j hj.1
              have h2 := hb j hj.1
              have hA := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl1) h1
              have hB := mul_nonpos_of_nonneg_of_nonpos hl0.le h2
              have h3 : l * fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, v0)) = 0 :=
                le_antisymm hB (by linarith only [hA, h0])
              rcases mul_eq_zero.1 h3 with h | h
              · exact absurd h hl0.ne'
              · rw [h, sub_zero]
            have hevne : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≠ 0 :=
              eventually_mem_nhdsWithin.mono (fun t ht => ne_of_gt ht)
            have hy0 : Tendsto (fun t => t⁻¹ • ((y + t • v0 + r0 t) - y)) (𝓝[>] 0) (𝓝 v0) := by
              have h1 : Tendsto (fun t : ℝ => v0 + t⁻¹ • r0 t) (𝓝[>] 0) (𝓝 v0) := by
                simpa using (tendsto_const_nhds (x := v0)).add hr0
              refine h1.congr' (hevne.mono fun t ht => ?_)
              show _ = t⁻¹ • (y + t • v0 + r0 t - y)
              rw [add_assoc, add_sub_cancel_left, smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul]
            obtain ⟨c, hc, hcev⟩ := hcore J w hJ hJw _ hy0
            refine ⟨fun t => r0 t + c t, by simpa using hr0.add hc, ?_⟩
            have hR : Tendsto (fun t : ℝ => t⁻¹ • (WithLp.toLp 2 ((0:E n), r0 t + c t) : Z n m))
                (𝓝[>] 0) (𝓝 0) := by
              have := (hc0.tendsto 0).comp (by simpa using hr0.add hc :
                Tendsto (fun t : ℝ => t⁻¹ • (r0 t + c t)) (𝓝[>] 0) (𝓝 0))
              simp only [Function.comp_def] at this
              have h00 : (WithLp.toLp 2 ((0:E n), (0:E m)) : Z n m) = 0 := rfl
              rw [h00] at this
              refine this.congr' (Eventually.of_forall fun t => ?_)
              show (WithLp.toLp 2 ((0:E n), t⁻¹ • (r0 t + c t)) : Z n m) =
                t⁻¹ • WithLp.toLp 2 ((0:E n), r0 t + c t)
              rw [heqs, smul_zero]
            have hpt : ∀ t : ℝ, z0 + (t • WithLp.toLp 2 (u, vl) + WithLp.toLp 2 ((0:E n), r0 t + c t))
                = WithLp.toLp 2 (x + t • u, y + t • vl + (r0 t + c t)) := by
              intro t; rw [hz0, heqs, heq, heq, add_zero, add_assoc]
            have hpt2 : ∀ t : ℝ, (y + t • v0 + r0 t) + t • w + c t = y + t • vl + (r0 t + c t) := by
              intro t; rw [hw, smul_sub]; abel
            have hall : ∀ j, ∀ᶠ t in 𝓝[>] (0:ℝ),
                g (WithLp.toLp 2 (x + t • u, y + t • vl + (r0 t + c t))) j ≤ 0 := by
              intro j
              have hL := hlim j (WithLp.toLp 2 (u, vl)) _ hR
              simp only [hpt] at hL
              by_cases hj0 : g z0 j = 0
              · by_cases hjJ : j ∈ J
                · filter_upwards [hcev, hev0] with t h1 h2
                  have := h1 j hjJ
                  rw [hpt2] at this
                  exact this.trans (h2 j)
                · have hneg : fderiv ℝ (fun z => g z j) z0 (WithLp.toLp 2 (u, vl)) < 0 :=
                    lt_of_le_of_ne (hvle j hj0) (fun h => hjJ ⟨hj0, h⟩)
                  filter_upwards [hL.eventually (gt_mem_nhds hneg), eventually_mem_nhdsWithin]
                    with t h1 ht
                  have ht' : (0:ℝ) < t := ht
                  rw [hj0, sub_zero, smul_eq_mul] at h1
                  have := (mul_neg_iff.1 h1)
                  rcases this with ⟨-, h⟩ | ⟨h, -⟩
                  · exact h.le
                  · exact absurd h (not_lt.2 (inv_nonneg.2 ht'.le))
              · have hneg : g z0 j < 0 := lt_of_le_of_ne (hy j) hj0
                have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
                have hm := ht.mul hL
                rw [zero_mul] at hm
                have hm2 : Tendsto (fun t : ℝ =>
                    g (WithLp.toLp 2 (x + t • u, y + t • vl + (r0 t + c t))) j - g z0 j)
                    (𝓝[>] 0) (𝓝 0) := by
                  refine hm.congr' (hevne.mono fun t ht => ?_)
                  simp only [smul_eq_mul]
                  field_simp
                filter_upwards [hm2.eventually (gt_mem_nhds (show (0:ℝ) < -g z0 j by linarith))]
                  with t h1
                linarith
            filter_upwards [Filter.eventually_all.2 hall] with t ht
            exact ht
          intro v hv
          apply happrox
          intro ε hε
          obtain ⟨l, hl0, hl1, hlε⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ l * ‖v - v0‖ ≤ ε / 2 := by
            refine ⟨min 1 (ε / 2 / (‖v - v0‖ + 1)), by positivity, min_le_left _ _, ?_⟩
            calc min 1 (ε / 2 / (‖v - v0‖ + 1)) * ‖v - v0‖
                ≤ ε / 2 / (‖v - v0‖ + 1) * (‖v - v0‖ + 1) := by
                  gcongr
                  · exact min_le_right _ _
                  · linarith
              _ = ε / 2 := by field_simp
          obtain ⟨r, hr, hev⟩ := hkey v hv l hl0 hl1
          have hr' : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖t⁻¹ • r t‖ < ε / 2 := by
            have := (Metric.tendsto_nhds.1 hr) (ε / 2) (by positivity)
            simpa [dist_zero_right] using this
          filter_upwards [hev, hr', eventually_mem_nhdsWithin] with t h1 h2 ht
          have ht' : (0:ℝ) < t := ht
          refine ⟨_, h1, ?_⟩
          rw [norm_smul, norm_inv, Real.norm_of_nonneg ht'.le, inv_mul_lt_iff₀ ht'] at h2
          have he : y + t • v - (y + t • ((1 - l) • v + l • v0) + r t) = (t * l) • (v - v0) - r t := by
            simp only [smul_add, smul_sub, smul_smul, sub_smul, one_smul]
            abel
          rw [he]
          calc ‖(t * l) • (v - v0) - r t‖ ≤ ‖(t * l) • (v - v0)‖ + ‖r t‖ := norm_sub_le _ _
            _ = t * (l * ‖v - v0‖) + ‖r t‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
            _ ≤ t * (ε / 2) + t * (ε / 2) := by gcongr
            _ = ε * t := by ring
