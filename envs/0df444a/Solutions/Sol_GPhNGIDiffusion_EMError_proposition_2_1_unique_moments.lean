-- Prove2me | solution 1 for GPhNGIDiffusion.EMError.proposition_2_1_unique_moments
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T17:56:31.236844+00:00
-- url     : https://prove2.me/submissions/296f63f0-44bd-4622-91ae-0f62b2376b90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Theorems.Thm_GPhNGIDiffusion_EMError_lyapunov_A4_A7
import Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_4
import Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_1_generator

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EMErrUniq
open GPhNGIDiffusion.EMError

lemma pi_ac : ∀ (n : ℕ) (μ ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
    (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  | 0, μ, ν, _, _, _ => by
    rw [Measure.pi_of_empty μ (fun i => i.elim0), Measure.pi_of_empty ν (fun i => i.elim0)]
  | n + 1, μ, ν, _, _, h => by
    have ih := pi_ac n (fun j => μ (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      (fun j => h _)
    have e1 := (measurePreserving_piFinSuccAbove μ 0)
    have e2 := (measurePreserving_piFinSuccAbove ν 0)
    have hp : ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) ≪
        ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))) :=
      (h 0).prod ih
    have k1 : Measure.pi μ = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))).map
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm := by
      rw [← e1.map_eq, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
      simp
    have k2 : Measure.pi ν = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))).map
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm := by
      rw [← e2.map_eq, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
      simp
    rw [k1, k2]
    exact hp.map (MeasurableEquiv.measurable _)

variable {d : ℕ}

lemma std_ac : stdGaussian (EthierKurtz.SDEState d) ≪ volume := by
  rw [← map_pi_eq_stdGaussian, ← (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  refine (pi_ac d _ _ (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)).map ?_
  fun_prop

lemma ac_std : volume ≪ stdGaussian (EthierKurtz.SDEState d) := by
  rw [← map_pi_eq_stdGaussian, ← (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  refine (pi_ac d _ _ (fun _ => gaussianReal_absolutelyContinuous' 0 one_ne_zero)).map ?_
  fun_prop

end EMErrUniq


open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Matrix

namespace EMErrUniq
open GPhNGIDiffusion.EMError

variable {d : ℕ}

lemma sigma_det (M : Model d) : M.σ.det ≠ 0 := by
  intro h
  have h' : M.σᵀ.det = 0 := by rw [Matrix.det_transpose]; exact h
  obtain ⟨v, hv, hσv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h'
  obtain ⟨c, hc, hell⟩ := M.hell
  have h1 := hell v
  have h2 : v ⬝ᵥ ((M.σ * M.σᵀ) *ᵥ v) = 0 := by
    rw [← Matrix.mulVec_mulVec, hσv, Matrix.mulVec_zero, dotProduct_zero]
  have h3 : 0 < v ⬝ᵥ v := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ v i * v i := fun i _ => mul_self_nonneg _
    rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; apply hv
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq.symm i (Finset.mem_univ _)
      simpa using this
  nlinarith

lemma kernel_meas (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (hb : Continuous b)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) : Measurable (emStep b σ η) := by
  have hT : Measurable (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
      q.1 + η • b q.1 + Real.sqrt η • mv σ q.2) := by
    apply Continuous.measurable; unfold mv; fun_prop
  have hT' : ∀ x, Measurable (fun z : EthierKurtz.SDEState d => x + η • b x + Real.sqrt η • mv σ z) :=
    fun x => hT.comp measurable_prodMk_left
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have : (fun x => emStep b σ η x s) = fun x => (stdGaussian (EthierKurtz.SDEState d)) (Prod.mk x ⁻¹' ((fun q :
      EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
      q.1 + η • b q.1 + Real.sqrt η • mv σ q.2) ⁻¹' s)) := by
    funext x; rw [emStep, Measure.map_apply (hT' x) hs]; rfl
  rw [this]; exact measurable_measure_prodMk_left (hT hs)

instance emStep_prob (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (σ : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (x : EthierKurtz.SDEState d) :
    IsProbabilityMeasure (emStep b σ η x) := by
  unfold emStep
  exact Measure.isProbabilityMeasure_map (Continuous.measurable (by unfold mv; fun_prop)).aemeasurable

lemma emStep_null (M : Model d) {η : ℝ} (hη : 0 < η) (x : EthierKurtz.SDEState d)
    {S : Set (EthierKurtz.SDEState d)} (hS : MeasurableSet S) :
    emStep M.drift M.σ η x S = 0 ↔ volume S = 0 := by
  let L : EthierKurtz.SDEState d →ₗ[ℝ] EthierKurtz.SDEState d :=
    Real.sqrt η • Matrix.toEuclideanLin M.σ
  have hL : ∀ z, Real.sqrt η • mv M.σ z = L z := by
    intro z; simp [L, mv, Matrix.toEuclideanLin_apply]
  have hdet : LinearMap.det L ≠ 0 := by
    intro h0
    have hk := LinearMap.bot_lt_ker_of_det_eq_zero h0
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk.ne'
    rw [LinearMap.mem_ker, ← hL] at hz
    have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
    have hmv : mv M.σ z = 0 := by
      rcases smul_eq_zero.mp hz with h | h
      · exact absurd h hs
      · exact h
    apply sigma_det M
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨WithLp.ofLp z, ?_, ?_⟩
    · intro h; apply hz0; exact (WithLp.ofLp_eq_zero 2).mp h
    · have := congrArg WithLp.ofLp hmv
      simpa [mv] using this
  set c := x + η • M.drift x
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hT : (fun z => x + η • M.drift x + Real.sqrt η • mv M.σ z) = (fun y => c + y) ∘ L := by
    funext z; simp [hL, c]
  have hTm : Measurable ((fun y => c + y) ∘ L) := (measurable_const_add c).comp hLm
  rw [emStep, hT, Measure.map_apply hTm hS]
  have hvol : volume (((fun y => c + y) ∘ L) ⁻¹' S) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * volume S := by
    rw [Set.preimage_comp, ← Measure.map_apply hLm ((measurable_const_add c) hS),
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, Measure.smul_apply, smul_eq_mul,
      ← Measure.map_apply (measurable_const_add c) hS, map_add_left_eq_self]
  have hk : ENNReal.ofReal |(LinearMap.det L)⁻¹| ≠ 0 := by
    simp [hdet]
  constructor
  · intro h
    have := (ac_std (d := d)) h
    rw [hvol] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hk
    · exact h'
  · intro h
    apply std_ac
    rw [hvol, h, mul_zero]

lemma em_unique (M : Model d) {η : ℝ} (hη : 0 < η) (μ1 μ2 : Measure (EthierKurtz.SDEState d))
    (h1 : IsEMInvariant M.drift M.σ η μ1) (h2 : IsEMInvariant M.drift M.σ η μ2) : μ1 = μ2 := by
  haveI := h1.1; haveI := h2.1
  by_contra hne
  have hbc : Continuous M.drift := by unfold Model.drift; fun_prop
  have hK := kernel_meas M.drift hbc M.σ η
  obtain ⟨S, hS, hle1, hle2⟩ := hahn_decomposition μ1 μ2
  set a := μ1.restrict S
  set b := μ2.restrict S
  set c := μ1.restrict Sᶜ
  set e := μ2.restrict Sᶜ
  have hba : b ≤ a := by
    refine Measure.le_iff.mpr (fun t ht => ?_)
    simp only [b, a, Measure.restrict_apply ht]
    exact hle1 _ (ht.inter hS) Set.inter_subset_right
  have hce : c ≤ e := by
    refine Measure.le_iff.mpr (fun t ht => ?_)
    simp only [c, e, Measure.restrict_apply ht]
    exact hle2 _ (ht.inter hS.compl) Set.inter_subset_right
  set p := a - b
  set q := e - c
  have ha : a = p + b := (Measure.sub_add_cancel_of_le hba).symm
  have he : e = q + c := (Measure.sub_add_cancel_of_le hce).symm
  set f : EthierKurtz.SDEState d → ℝ≥0∞ := fun x => emStep M.drift M.σ η x S
  have hf : Measurable f := Measure.measurable_coe hS |>.comp hK
  have hf1 : ∀ x, f x ≤ 1 := fun x => prob_le_one
  have hμ1 : μ1 = a + c := (Measure.restrict_add_restrict_compl hS).symm
  have hμ2 : μ2 = b + e := (Measure.restrict_add_restrict_compl hS).symm
  have inv : ∀ μ : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μ →
      μ S = ∫⁻ x, f x ∂μ := by
    intro μ hμ
    conv_lhs => rw [← hμ.2]
    rw [Measure.bind_apply hS hK.aemeasurable]
  have E1 := inv μ1 h1
  have E2 := inv μ2 h2
  have ha_univ : μ1 S = a Set.univ := by simp [a]
  have hb_univ : μ2 S = b Set.univ := by simp [b]
  rw [ha_univ, hμ1, lintegral_add_measure, ha, lintegral_add_measure, Measure.add_apply] at E1
  rw [hb_univ, hμ2, lintegral_add_measure, he, lintegral_add_measure] at E2
  -- finiteness
  have fin_b : b Set.univ ≠ ⊤ := measure_ne_top _ _
  have hX : ∫⁻ x, f x ∂p ≤ p Set.univ := by
    calc ∫⁻ x, f x ∂p ≤ ∫⁻ _, 1 ∂p := lintegral_mono hf1
      _ = p Set.univ := by simp
  have hpfin : p Set.univ ≠ ⊤ := by
    have : p Set.univ ≤ μ1 Set.univ := by
      rw [hμ1, ha]; simp only [Measure.add_apply]; exact le_self_add.trans le_self_add
    exact ne_top_of_le_ne_top (measure_ne_top _ _) this
  have hZ : ∫⁻ x, f x ∂b ≠ ⊤ := by
    refine ne_top_of_le_ne_top fin_b ?_
    calc ∫⁻ x, f x ∂b ≤ ∫⁻ _, 1 ∂b := lintegral_mono hf1
      _ = b Set.univ := by simp
  have hY : ∫⁻ x, f x ∂c ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top c Set.univ) ?_
    calc ∫⁻ x, f x ∂c ≤ ∫⁻ _, 1 ∂c := lintegral_mono hf1
      _ = c Set.univ := by simp
  -- p U + W = X
  have key : p Set.univ + ∫⁻ x, f x ∂q = ∫⁻ x, f x ∂p := by
    have hsum : p Set.univ + (∫⁻ x, f x ∂q) + (∫⁻ x, f x ∂b + ∫⁻ x, f x ∂c) =
        ∫⁻ x, f x ∂p + (∫⁻ x, f x ∂b + ∫⁻ x, f x ∂c) := by
      calc p Set.univ + (∫⁻ x, f x ∂q) + (∫⁻ x, f x ∂b + ∫⁻ x, f x ∂c)
          = p Set.univ + (∫⁻ x, f x ∂b + (∫⁻ x, f x ∂q + ∫⁻ x, f x ∂c)) := by ring
        _ = p Set.univ + b Set.univ := by rw [E2]
        _ = ∫⁻ x, f x ∂p + ∫⁻ x, f x ∂b + ∫⁻ x, f x ∂c := E1
        _ = _ := by ring
    exact (ENNReal.add_left_inj (ENNReal.add_ne_top.mpr ⟨hZ, hY⟩)).mp hsum
  have hW : ∫⁻ x, f x ∂q = 0 := by
    have : p Set.univ + ∫⁻ x, f x ∂q ≤ p Set.univ + 0 := by rw [key, add_zero]; exact hX
    exact le_antisymm ((ENNReal.add_le_add_iff_left hpfin).mp this) bot_le
  have hXp : ∫⁻ x, f x ∂p = p Set.univ := by rw [← key, hW, add_zero]
  -- masses
  have hmass : p Set.univ = q Set.univ := by
    have m1 : μ1 Set.univ = μ2 Set.univ := by simp
    rw [hμ1, hμ2, ha, he] at m1
    simp only [Measure.add_apply] at m1
    have m2 : p Set.univ + (b Set.univ + c Set.univ) = q Set.univ + (b Set.univ + c Set.univ) := by
      calc _ = p Set.univ + b Set.univ + c Set.univ := by ring
        _ = b Set.univ + (q Set.univ + c Set.univ) := m1
        _ = _ := by ring
    exact (ENNReal.add_left_inj (ENNReal.add_ne_top.mpr ⟨fin_b, measure_ne_top _ _⟩)).mp m2
  have hp0 : p ≠ 0 := by
    intro hp
    have hq : q = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← hmass, hp]; simp
    apply hne
    rw [hμ1, hμ2, ha, he, hp, hq, zero_add, zero_add]
  have hq0 : q ≠ 0 := by
    intro hq; apply hp0
    rw [← Measure.measure_univ_eq_zero, hmass, hq]; simp
  -- find y with f y = 0
  have hae : f =ᵐ[q] 0 := (lintegral_eq_zero_iff hf).mp hW
  haveI : (ae q).NeBot := ae_neBot.mpr hq0
  obtain ⟨y, hy⟩ := hae.exists
  -- find x with f x = 1
  have hsub : ∫⁻ x, (1 - f x) ∂p = 0 := by
    rw [lintegral_sub hf (by rw [hXp]; exact hpfin) (ae_of_all _ hf1), hXp]
    simp
  have hae2 : (fun x => 1 - f x) =ᵐ[p] 0 :=
    (lintegral_eq_zero_iff (measurable_const.sub hf)).mp hsub
  haveI : (ae p).NeBot := ae_neBot.mpr hp0
  obtain ⟨x, hx⟩ := hae2.exists
  have hx1 : f x = 1 := le_antisymm (hf1 x) (tsub_eq_zero_iff_le.mp hx)
  have hxc : emStep M.drift M.σ η x Sᶜ = 0 := by
    rw [prob_compl_eq_one_sub hS]; simp only [f] at hx1; rw [hx1]; simp
  have hvol : volume Sᶜ = 0 := (emStep_null M hη x hS.compl).mp hxc
  have hyc : emStep M.drift M.σ η y Sᶜ = 0 := (emStep_null M hη y hS.compl).mpr hvol
  rw [prob_compl_eq_zero_iff hS] at hyc
  simp only [f, Pi.zero_apply] at hy
  rw [hy] at hyc
  exact zero_ne_one hyc

end EMErrUniq


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace EMErrMom

variable {X : Type*} [MeasurableSpace X]

/-- If `μ` is invariant for a Markov kernel `K` and `K W ≤ γ W + B` with `γ < 1`, then
`μ(W) ≤ B / (1 - γ)`. -/
lemma inv_lyap (K : X → Measure X) (hK : Measurable K) (hKp : ∀ x, IsProbabilityMeasure (K x))
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : μ.bind K = μ)
    (W : X → ℝ≥0∞) (hW : Measurable W) (hWfin : ∀ x, W x ≠ ⊤)
    (γ B : ℝ≥0∞) (hγ : γ < 1)
    (hdrift : ∀ x, ∫⁻ y, W y ∂(K x) ≤ γ * W x + B) :
    ∫⁻ x, W x ∂μ ≤ B * (1 - γ)⁻¹ := by
  set C := B * (1 - γ)⁻¹
  have hinv : ∀ g : X → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = ∫⁻ x, (∫⁻ y, g y ∂(K x)) ∂μ := by
    intro g hg
    conv_lhs => rw [← hμ]
    exact Measure.lintegral_bind hK.aemeasurable hg.aemeasurable
  -- truncation level
  have htrunc : ∀ N : ℝ≥0∞, N ≠ ⊤ → ∫⁻ x, min (W x) N ∂μ ≤ C := by
    intro N hN
    -- g k x = min (γ^k W x + S_k) N, S_k = B * ∑_{j<k} γ^j
    let S : ℕ → ℝ≥0∞ := fun k => B * ∑ j ∈ Finset.range k, γ ^ j
    let g : ℕ → X → ℝ≥0∞ := fun k x => min (γ ^ k * W x + S k) N
    have hg : ∀ k, Measurable (g k) := fun k =>
      ((measurable_const.mul hW).add measurable_const).min measurable_const
    have step : ∀ k, ∫⁻ x, g k x ∂μ ≤ ∫⁻ x, g (k+1) x ∂μ := by
      intro k
      rw [hinv _ (hg k)]
      refine lintegral_mono (fun x => ?_)
      haveI := hKp x
      refine le_min ?_ ?_
      · calc ∫⁻ y, g k y ∂(K x) ≤ ∫⁻ y, (γ ^ k * W y + S k) ∂(K x) :=
              lintegral_mono (fun y => min_le_left _ _)
          _ = γ ^ k * ∫⁻ y, W y ∂(K x) + S k := by
              rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hW]; simp
          _ ≤ γ ^ k * (γ * W x + B) + S k := by gcongr; exact hdrift x
          _ = γ ^ (k+1) * W x + S (k+1) := by
              simp only [S, Finset.sum_range_succ, mul_add, pow_succ]; ring
      · calc ∫⁻ y, g k y ∂(K x) ≤ ∫⁻ _, N ∂(K x) := lintegral_mono (fun y => min_le_right _ _)
          _ = N := by simp
    have chain : ∀ k, ∫⁻ x, min (W x) N ∂μ ≤ ∫⁻ x, g k x ∂μ := by
      intro k
      induction k with
      | zero => exact le_of_eq (by congr 1; funext x; simp [g, S])
      | succ k ih => exact ih.trans (step k)
    have hS : ∀ k, S k ≤ C := by
      intro k
      simp only [S, C]
      gcongr
      rw [← ENNReal.tsum_geometric]
      exact ENNReal.sum_le_tsum _
    have bound : ∀ k, ∫⁻ x, min (W x) N ∂μ ≤ ∫⁻ x, min (γ ^ k * W x + C) N ∂μ := by
      intro k
      refine (chain k).trans (lintegral_mono (fun x => ?_))
      exact min_le_min_right _ (add_le_add_right (hS k) _)
    have hlim : Tendsto (fun k => ∫⁻ x, min (γ ^ k * W x + C) N ∂μ) atTop
        (𝓝 (∫⁻ x, min (0 * W x + C) N ∂μ)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => N) (fun k => ?_)
        (fun k => ae_of_all _ (fun x => min_le_right _ _)) (by simpa using hN) (ae_of_all _ ?_)
      · exact ((measurable_const.mul hW).add measurable_const).min measurable_const
      · intro x
        have h0 : Tendsto (fun k : ℕ => γ ^ k) atTop (𝓝 0) :=
          ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hγ
        have h1 : Tendsto (fun k : ℕ => γ ^ k * W x) atTop (𝓝 (0 * W x)) :=
          ENNReal.Tendsto.mul_const h0 (Or.inr (hWfin x))
        have h2 : Tendsto (fun k : ℕ => γ ^ k * W x + C) atTop (𝓝 (0 * W x + C)) :=
          h1.add tendsto_const_nhds
        exact h2.min tendsto_const_nhds
    have := ge_of_tendsto' hlim bound
    refine this.trans ?_
    calc ∫⁻ x, min (0 * W x + C) N ∂μ ≤ ∫⁻ _, C ∂μ := by
          refine lintegral_mono (fun x => ?_); simp
      _ = C := by simp
  -- monotone convergence
  have hsup : ∀ x, W x = ⨆ n : ℕ, min (W x) (n : ℝ≥0∞) := by
    intro x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]; simp
  calc ∫⁻ x, W x ∂μ = ∫⁻ x, ⨆ n : ℕ, min (W x) (n : ℝ≥0∞) ∂μ := by
        congr 1; funext x; exact hsup x
    _ = ⨆ n : ℕ, ∫⁻ x, min (W x) (n : ℝ≥0∞) ∂μ := by
        refine lintegral_iSup (fun n => hW.min measurable_const) ?_
        intro m n hmn x
        exact min_le_min_left _ (by exact_mod_cast hmn)
    _ ≤ C := iSup_le (fun n => htrunc n (ENNReal.natCast_ne_top n))

end EMErrMom


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace EMErrKB

variable {d : ℕ}


lemma integral_bind_bcf (κ : Kernel (EthierKurtz.SDEState d) (EthierKurtz.SDEState d)) [IsMarkovKernel κ] (μ : Measure (EthierKurtz.SDEState d))
    [IsProbabilityMeasure μ] (f : (EthierKurtz.SDEState d) →ᵇ ℝ) :
    ∫ y, f y ∂(μ.bind κ) = ∫ x, ∫ y, f y ∂(κ x) ∂μ := by
  rw [← Measure.snd_compProd μ κ, Measure.snd, integral_map measurable_snd.aemeasurable
    f.continuous.aestronglyMeasurable]
  rw [Measure.integral_compProd (f := fun p : (EthierKurtz.SDEState d) × (EthierKurtz.SDEState d) => f p.2)]
  exact (f.integrable _).comp_measurable measurable_snd

lemma kb_exists (κ : Kernel (EthierKurtz.SDEState d) (EthierKurtz.SDEState d)) [IsMarkovKernel κ]
    (hFeller : ∀ f : (EthierKurtz.SDEState d) →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂(κ x))
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (L : ℕ → Measure (EthierKurtz.SDEState d)) (hL0 : L 0 = Measure.dirac 0)
    (hLs : ∀ k, L (k+1) = (L k).bind κ) (hmom : ∀ k, ∫⁻ x, ‖x‖ₑ ∂(L k) ≤ B) :
    ∃ μ : Measure (EthierKurtz.SDEState d), IsProbabilityMeasure μ ∧ μ.bind κ = μ := by
  have hLp : ∀ k, IsProbabilityMeasure (L k) := by
    intro k
    induction k with
    | zero => rw [hL0]; infer_instance
    | succ k ih =>
      rw [hLs k]
      constructor
      rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
      simp
  -- Cesàro averages
  let νm : ℕ → Measure (EthierKurtz.SDEState d) := fun n => ((n : ℝ≥0∞) + 1)⁻¹ • ∑ k ∈ Finset.range (n+1), L k
  have hνp : ∀ n, IsProbabilityMeasure (νm n) := by
    intro n
    constructor
    simp only [νm, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  let ν : ℕ → ProbabilityMeasure (EthierKurtz.SDEState d) := fun n => ⟨νm n, hνp n⟩
  have hint : ∀ (g : (EthierKurtz.SDEState d) →ᵇ ℝ) n, ∫ x, g x ∂(ν n : Measure (EthierKurtz.SDEState d)) =
      ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n+1), ∫ x, g x ∂(L k) := by
    intro g n
    change ∫ x, g x ∂(νm n) = _
    simp only [νm]
    rw [integral_smul_measure, integral_finset_sum_measure (fun k _ => g.integrable _)]
    simp [ENNReal.toReal_inv, smul_eq_mul]
    left; norm_cast
  -- tightness
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure (EthierKurtz.SDEState d)) : Measure (EthierKurtz.SDEState d)) | μ ∈ Set.range ν} := by
    apply isTightMeasureSet_of_tendsto_measure_norm_gt
    have hmk : ∀ (μ : Measure (EthierKurtz.SDEState d)), (∫⁻ x, ‖x‖ₑ ∂μ ≤ B) → ∀ r : ℝ, 0 < r →
        μ {x | r < ‖x‖} ≤ B / ENNReal.ofReal r := by
      intro μ hμ r hr
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hr)) (Or.inl ENNReal.ofReal_ne_top)]
      calc μ {x | r < ‖x‖} * ENNReal.ofReal r = ENNReal.ofReal r * μ {x | r < ‖x‖} := mul_comm _ _
        _ ≤ ENNReal.ofReal r * μ {x | ENNReal.ofReal r ≤ ‖x‖ₑ} := by
            refine mul_le_mul' le_rfl (measure_mono (fun x hx => ?_))
            simp only [Set.mem_setOf_eq] at hx ⊢
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal hx.le
        _ ≤ ∫⁻ x, ‖x‖ₑ ∂μ := mul_meas_ge_le_lintegral₀ (by fun_prop) _
        _ ≤ B := hμ
    have hνmom : ∀ n, ∫⁻ x, ‖x‖ₑ ∂(νm n) ≤ B := by
      intro n
      simp only [νm]
      rw [lintegral_smul_measure, lintegral_finset_sum_measure]
      calc ((n : ℝ≥0∞) + 1)⁻¹ * ∑ k ∈ Finset.range (n+1), ∫⁻ x, ‖x‖ₑ ∂(L k)
          ≤ ((n : ℝ≥0∞) + 1)⁻¹ * ∑ k ∈ Finset.range (n+1), B := by
            gcongr with k; exact hmom k
        _ = B := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
            push_cast
            rw [ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    have hup : ∀ᶠ r : ℝ in atTop, (⨆ μ ∈ {((μ : ProbabilityMeasure (EthierKurtz.SDEState d)) : Measure (EthierKurtz.SDEState d)) | μ ∈ Set.range ν},
        μ {x | r < ‖x‖}) ≤ B / ENNReal.ofReal r := by
      filter_upwards [eventually_gt_atTop 0] with r hr
      refine iSup₂_le (fun μ hμ => ?_)
      obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hμ
      exact hmk _ (hνmom n) r hr
    have hlim : Tendsto (fun r : ℝ => B / ENNReal.ofReal r) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal r) atTop (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop
      have := ENNReal.Tendsto.div tendsto_const_nhds (Or.inr ENNReal.top_ne_zero) h1 (Or.inr hB)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun _ => bot_le)) hup
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨μ, -, φ, hφ, hconv⟩ := hcomp.tendsto_subseq (x := ν) (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨(μ : Measure (EthierKurtz.SDEState d)), inferInstance, ?_⟩
  -- the identity on bounded continuous functions
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  let Kf : (EthierKurtz.SDEState d) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fun x => ∫ y, f y ∂(κ x), hFeller f⟩
    (2 * ‖f‖) (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hb : ∀ z, |∫ y, f y ∂(κ z)| ≤ ‖f‖ := by
        intro z
        have := norm_integral_le_of_norm_le_const (μ := κ z) (C := ‖f‖)
          (Eventually.of_forall (fun y => f.norm_coe_le_norm y))
        simpa using this
      calc |∫ y, f y ∂(κ x) - ∫ y, f y ∂(κ y)| ≤ |∫ y, f y ∂(κ x)| + |∫ y, f y ∂(κ y)| :=
            abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (hb x) (hb y)
        _ = 2 * ‖f‖ := by ring)
  have hKf : ∀ x, Kf x = ∫ y, f y ∂(κ x) := fun x => rfl
  have hstep : ∀ k, ∫ x, Kf x ∂(L k) = ∫ x, f x ∂(L (k+1)) := by
    intro k
    haveI := hLp k
    rw [hLs k, integral_bind_bcf κ (L k) f]
    rfl
  have hdiff : ∀ n, ∫ x, Kf x ∂(ν n : Measure (EthierKurtz.SDEState d)) - ∫ x, f x ∂(ν n : Measure (EthierKurtz.SDEState d)) =
      ((n : ℝ) + 1)⁻¹ * (∫ x, f x ∂(L (n+1)) - ∫ x, f x ∂(L 0)) := by
    intro n
    rw [hint, hint, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    simp_rw [hstep]
    exact Finset.sum_range_sub (fun k => ∫ x, f x ∂(L k)) (n+1)
  have hbd : ∀ k, |∫ x, f x ∂(L k)| ≤ ‖f‖ := by
    intro k
    haveI := hLp k
    have := norm_integral_le_of_norm_le_const (μ := L k) (C := ‖f‖)
      (Eventually.of_forall (fun y => f.norm_coe_le_norm y))
    simpa using this
  have hzero : Tendsto (fun n => ∫ x, Kf x ∂(ν (φ n) : Measure (EthierKurtz.SDEState d)) -
      ∫ x, f x ∂(ν (φ n) : Measure (EthierKurtz.SDEState d))) atTop (𝓝 0) := by
    simp_rw [hdiff]
    have hc : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (φ n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      exact h1.inv_tendsto_atTop
    have hb : ∀ n, |∫ x, f x ∂(L (φ n + 1)) - ∫ x, f x ∂(L 0)| ≤ 2 * ‖f‖ := by
      intro n
      calc _ ≤ |∫ x, f x ∂(L (φ n + 1))| + |∫ x, f x ∂(L 0)| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (hbd _) (hbd _)
        _ = _ := by ring
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hc.mul_const (2 * ‖f‖))
    rw [Real.norm_eq_abs, abs_mul, abs_inv]
    have hpos : (0 : ℝ) < (φ n : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left (hb n) (by positivity)
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) Kf
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  have h3 := h1.sub h2
  have heq : ∫ x, Kf x ∂(μ : Measure (EthierKurtz.SDEState d)) - ∫ x, f x ∂(μ : Measure (EthierKurtz.SDEState d)) = 0 :=
    tendsto_nhds_unique h3 hzero
  rw [integral_bind_bcf κ (μ : Measure (EthierKurtz.SDEState d)) f]
  simp only [← hKf]
  linarith

end EMErrKB


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
open Matrix

namespace EMErrP21
open GPhNGIDiffusion.EMError

variable {d : ℕ}

/-- Real-variable estimate for the drift constants of Lemma A.4 for small `η`. -/
lemma small_eta (c₁ cℓ Ct : ℝ) (hc1 : 0 < c₁) (hcl : 0 ≤ cℓ) (hCt : 0 < Ct) :
    ∃ η' : ℝ, 0 < η' ∧ ∀ η : ℝ, 0 < η → η ≤ η' →
      c₁ * η / 4 ≤ 1 - (Real.exp (-c₁ * η) + Ct * η ^ (3 / 2 : ℝ)) ∧
      cℓ / c₁ * (1 - Real.exp (-c₁ * η)) + Ct * η ^ (3 / 2 : ℝ) ≤ (cℓ + c₁ / 4) * η := by
  refine ⟨min (1 / c₁) ((c₁ / (4 * Ct)) ^ 2), by positivity, fun η hη hle => ?_⟩
  have hη1 : c₁ * η ≤ 1 := by
    have := hle.trans (min_le_left _ _)
    rw [le_div_iff₀ hc1] at this; linarith
  have hη2 : η ≤ (c₁ / (4 * Ct)) ^ 2 := hle.trans (min_le_right _ _)
  have hsq : Real.sqrt η ≤ c₁ / (4 * Ct) := by
    rw [Real.sqrt_le_left (by positivity)]; exact hη2
  have hpow : η ^ (3 / 2 : ℝ) = η * Real.sqrt η := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hη.le (by norm_num)]
    norm_num
  have hCtη : Ct * η ^ (3 / 2 : ℝ) ≤ c₁ * η / 4 := by
    rw [hpow]
    calc Ct * (η * Real.sqrt η) = η * (Ct * Real.sqrt η) := by ring
      _ ≤ η * (Ct * (c₁ / (4 * Ct))) := by gcongr
      _ = c₁ * η / 4 := by field_simp
  set t := c₁ * η
  have ht : 0 < t := by positivity
  have hexp1 : Real.exp (-t) ≤ 1 - t / 2 := by
    -- e^{-t} ≤ 1/(1+t) ≤ 1 - t/2 for t ≤ 1
    have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h2 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    rw [h2]
    have hpos : 0 < 1 + t := by linarith
    calc (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := by
          exact inv_anti₀ hpos h1
      _ ≤ 1 - t / 2 := by
          rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
  have hexp2 : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hneg : -c₁ * η = -t := by ring
  rw [hneg]
  constructor
  · linarith
  · have : cℓ / c₁ * (1 - Real.exp (-t)) ≤ cℓ / c₁ * t := by
      gcongr
    have h3 : cℓ / c₁ * t = cℓ * η := by simp only [t]; field_simp
    nlinarith

/-- Moment bound for invariant measures from the drift inequality. -/
lemma inv_bound (M : Model d) {η : ℝ} (W : EthierKurtz.SDEState d → ℝ) (hWc : Continuous W)
    (hW0 : ∀ x, 0 ≤ W x) (γ K : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hK : 0 ≤ K)
    (hdrift : ∀ x, ∫⁻ y, ENNReal.ofReal (W y) ∂(emStep M.drift M.σ η x) ≤
      ENNReal.ofReal (γ * W x + K))
    (μt : Measure (EthierKurtz.SDEState d)) (hμt : IsEMInvariant M.drift M.σ η μt) :
    ∫⁻ x, ENNReal.ofReal (W x) ∂μt ≤ ENNReal.ofReal (K / (1 - γ)) := by
  haveI := hμt.1
  have hbc : Continuous M.drift := by unfold Model.drift; fun_prop
  have := EMErrMom.inv_lyap (emStep M.drift M.σ η) (EMErrUniq.kernel_meas M.drift hbc M.σ η)
    (fun x => inferInstance) μt hμt.2 (fun x => ENNReal.ofReal (W x))
    (hWc.measurable.ennreal_ofReal) (fun x => ENNReal.ofReal_ne_top)
    (ENNReal.ofReal γ) (ENNReal.ofReal K) (by rw [ENNReal.ofReal_lt_one]; exact hγ)
    (fun x => by
      refine (hdrift x).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by have := hW0 x; positivity) hK, ENNReal.ofReal_mul hγ0])
  refine this.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hγ0, ← ENNReal.ofReal_inv_of_pos (by linarith),
    ← ENNReal.ofReal_mul hK, div_eq_mul_inv]

lemma norm_pow_le (a : ℝ) (ha : 0 < a) (W : EthierKurtz.SDEState d → ℝ)
    (hW : ∀ y, a * ‖y‖ ^ 2 ≤ W y) (ℓ : ℕ) (x : EthierKurtz.SDEState d) :
    ‖x‖ ^ ℓ ≤ 1 + (1 / a) ^ ℓ * W x ^ ℓ := by
  have h1 : ‖x‖ ^ ℓ ≤ 1 + (‖x‖ ^ 2) ^ ℓ := by
    rcases le_or_gt ‖x‖ 1 with h | h
    · have : ‖x‖ ^ ℓ ≤ 1 := pow_le_one₀ (norm_nonneg _) h
      have : 0 ≤ (‖x‖ ^ 2) ^ ℓ := by positivity
      linarith
    · have : ‖x‖ ^ ℓ ≤ (‖x‖ ^ 2) ^ ℓ := by
        rw [← pow_mul]; exact pow_le_pow_right₀ h.le (by omega)
      linarith
  have h2 : (‖x‖ ^ 2) ^ ℓ ≤ (1 / a) ^ ℓ * W x ^ ℓ := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha, mul_comm]; exact hW x
  linarith

lemma emStep_feller (M : Model d) (η : ℝ) (f : EthierKurtz.SDEState d →ᵇ ℝ) :
    Continuous fun x => ∫ y, f y ∂(emStep M.drift M.σ η x) := by
  have hbc : Continuous M.drift := by unfold Model.drift; fun_prop
  have hT : Continuous (fun q : EthierKurtz.SDEState d × EthierKurtz.SDEState d =>
      q.1 + η • M.drift q.1 + Real.sqrt η • mv M.σ q.2) := by unfold mv; fun_prop
  have heq : (fun x => ∫ y, f y ∂(emStep M.drift M.σ η x)) =
      fun x => ∫ z, f (x + η • M.drift x + Real.sqrt η • mv M.σ z)
        ∂(stdGaussian (EthierKurtz.SDEState d)) := by
    funext x
    have hTx : Measurable (fun z : EthierKurtz.SDEState d =>
        x + η • M.drift x + Real.sqrt η • mv M.σ z) := Continuous.measurable (by unfold mv; fun_prop)
    rw [emStep, integral_map hTx.aemeasurable f.continuous.aestronglyMeasurable]
  rw [heq]
  refine continuous_of_dominated (bound := fun _ => ‖f‖) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact (f.continuous.comp (hT.comp (Continuous.prodMk_right x))).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => f.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Eventually.of_forall (fun z => f.continuous.comp (hT.comp (Continuous.prodMk_left z)))

end EMErrP21

open GPhNGIDiffusion.EMError EMErrP21 in
theorem solution {d : ℕ} (M : Model d) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      (∀ η : ℝ, 0 < η → η ≤ η₀ → ∃! μt : Measure (EthierKurtz.SDEState d),
        IsEMInvariant M.drift M.σ η μt) ∧
      (∀ ℓ : ℕ, 2 ≤ ℓ → ∃ ηℓ : ℝ, 0 < ηℓ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ ηℓ →
        ∀ μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt →
          ∫⁻ x, ‖x‖ₑ ^ ℓ ∂μt ≤ ENNReal.ofReal C) := by
  obtain ⟨Q, κ, c2, c₁, c₁', -, -, -, -, -, -, hV⟩ := lyapunov_A4_A7 M
  set V := lyapunovA4 M Q κ c2 with hVdef
  have hV' := hV
  obtain ⟨hVc2, hV0, ⟨a, A, B0, ha, hA, hB0, hVq⟩, -, hc1, hc1', hgen1⟩ := hV'
  have hVc : Continuous V := hVc2.continuous
  have hbc : Continuous M.drift := by unfold Model.drift; fun_prop
  -- drift for ℓ = 1
  have hgen1' : ∀ x, generator M.drift M.σ (fun y => V y ^ 1) x ≤ -c₁ * V x ^ 1 + c₁' := by
    intro x
    have hf : (fun y => V y ^ 1) = V := by funext y; simp
    rw [hf, pow_one]; exact hgen1 x
  obtain ⟨Ct1, hCt1, η1, hη1, -, hA41⟩ := lemma_A_4 M V c₁ c₁' hV 1 le_rfl c₁' hc1' hgen1'
  obtain ⟨η1', hη1', hsm1⟩ := small_eta c₁ c₁' Ct1 hc1 hc1'.le hCt1
  refine ⟨min η1 η1', lt_min hη1 hη1', ?_, ?_⟩
  · intro η hη hle
    have hle1 : η ≤ η1 := hle.trans (min_le_left _ _)
    have hle2 : η ≤ η1' := hle.trans (min_le_right _ _)
    obtain ⟨hγ1, hdr⟩ := hA41 η hη hle1
    obtain ⟨hgap, hKle⟩ := hsm1 η hη hle2
    set γ := Real.exp (-c₁ * η) + Ct1 * η ^ (3 / 2 : ℝ)
    set K := c₁' / c₁ * (1 - Real.exp (-c₁ * η)) + Ct1 * η ^ (3 / 2 : ℝ)
    have hγ0 : 0 ≤ γ := by positivity
    have hK0 : 0 ≤ K := by
      have : 0 ≤ 1 - Real.exp (-c₁ * η) := by
        rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
      positivity
    have hdrift : ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂(emStep M.drift M.σ η x) ≤
        ENNReal.ofReal (γ * V x + K) := by
      intro x; simpa using hdr x
    -- existence
    let κk : Kernel (EthierKurtz.SDEState d) (EthierKurtz.SDEState d) :=
      ⟨emStep M.drift M.σ η, EMErrUniq.kernel_meas M.drift hbc M.σ η⟩
    haveI : IsMarkovKernel κk := ⟨fun x => EMErrUniq.emStep_prob _ _ _ x⟩
    set M0 : ℝ := V 0 + K / (1 - γ)
    have hM0 : 0 ≤ M0 := by
      have : 0 ≤ K / (1 - γ) := div_nonneg hK0 (by linarith)
      have := hV0 0; positivity
    have hLp : ∀ k, IsProbabilityMeasure (emLaw M.drift M.σ η (Measure.dirac 0) k) := by
      intro k
      induction k with
      | zero => simp only [emLaw]; infer_instance
      | succ k ih =>
        simp only [emLaw]
        constructor
        rw [Measure.bind_apply MeasurableSet.univ
          (EMErrUniq.kernel_meas M.drift hbc M.σ η).aemeasurable]
        simp
    have hmV : ∀ k, ∫⁻ x, ENNReal.ofReal (V x) ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) ≤
        ENNReal.ofReal M0 := by
      intro k
      induction k with
      | zero =>
        simp only [emLaw]
        rw [lintegral_dirac' _ (hVc.measurable.ennreal_ofReal)]
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ K / (1 - γ) := div_nonneg hK0 (by linarith)
        linarith
      | succ k ih =>
        haveI := hLp k
        simp only [emLaw]
        rw [Measure.lintegral_bind (EMErrUniq.kernel_meas M.drift hbc M.σ η).aemeasurable
          (hVc.measurable.ennreal_ofReal).aemeasurable]
        calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (V y) ∂(emStep M.drift M.σ η x)
              ∂(emLaw M.drift M.σ η (Measure.dirac 0) k)
            ≤ ∫⁻ x, (ENNReal.ofReal γ * ENNReal.ofReal (V x) + ENNReal.ofReal K)
              ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) := by
              refine lintegral_mono (fun x => (hdrift x).trans (le_of_eq ?_))
              rw [ENNReal.ofReal_add (by have := hV0 x; positivity) hK0, ENNReal.ofReal_mul hγ0]
          _ = ENNReal.ofReal γ * ∫⁻ x, ENNReal.ofReal (V x)
              ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) + ENNReal.ofReal K := by
              rw [lintegral_add_right _ measurable_const,
                lintegral_const_mul _ (hVc.measurable.ennreal_ofReal)]
              simp
          _ ≤ ENNReal.ofReal γ * ENNReal.ofReal M0 + ENNReal.ofReal K := by gcongr
          _ = ENNReal.ofReal (γ * M0 + K) := by
              rw [ENNReal.ofReal_add (by positivity) hK0, ENNReal.ofReal_mul hγ0]
          _ ≤ ENNReal.ofReal M0 := by
              apply ENNReal.ofReal_le_ofReal
              have h1 : (1 - γ) * (K / (1 - γ)) = K := mul_div_cancel₀ K (by linarith)
              have h2 : 0 ≤ (1 - γ) * V 0 := mul_nonneg (by linarith) (hV0 0)
              simp only [M0]; nlinarith
    have hmom : ∀ k, ∫⁻ x, ‖x‖ₑ ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) ≤
        1 + ENNReal.ofReal (1 / a) * ENNReal.ofReal M0 := by
      intro k
      haveI := hLp k
      calc ∫⁻ x, ‖x‖ₑ ∂(emLaw M.drift M.σ η (Measure.dirac 0) k)
          ≤ ∫⁻ x, (1 + ENNReal.ofReal (1 / a) * ENNReal.ofReal (V x))
            ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) := by
            refine lintegral_mono (fun x => ?_)
            have := norm_pow_le a ha V (fun y => (hVq y).1) 1 x
            simp only [pow_one] at this
            rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
              ← ENNReal.ofReal_add zero_le_one (by have := hV0 x; positivity)]
            exact ENNReal.ofReal_le_ofReal this
        _ = 1 + ENNReal.ofReal (1 / a) * ∫⁻ x, ENNReal.ofReal (V x)
            ∂(emLaw M.drift M.σ η (Measure.dirac 0) k) := by
            rw [lintegral_add_left measurable_const,
              lintegral_const_mul _ (hVc.measurable.ennreal_ofReal)]
            simp
        _ ≤ _ := by gcongr; exact hmV k
    obtain ⟨μe, hμe, hμbind⟩ := EMErrKB.kb_exists κk (emStep_feller M η)
      (1 + ENNReal.ofReal (1 / a) * ENNReal.ofReal M0) (by finiteness)
      (emLaw M.drift M.σ η (Measure.dirac 0)) rfl (fun k => rfl) hmom
    refine ⟨μe, ⟨hμe, hμbind⟩, fun μ' hμ' => ?_⟩
    exact EMErrUniq.em_unique M hη μ' μe hμ' ⟨hμe, hμbind⟩
  · intro ℓ hℓ
    obtain ⟨cℓ, hcℓ, hgenℓ⟩ := lemma_A_1_generator M V c₁ c₁' hV ℓ (by omega)
    obtain ⟨Ct, hCt, ηℓ, hηℓ, -, hA4⟩ := lemma_A_4 M V c₁ c₁' hV ℓ (by omega) cℓ hcℓ hgenℓ
    obtain ⟨ηs, hηs, hsm⟩ := small_eta c₁ cℓ Ct hc1 hcℓ.le hCt
    refine ⟨min ηℓ ηs, lt_min hηℓ hηs, 1 + (1 / a) ^ ℓ * (4 * cℓ / c₁ + 1), ?_⟩
    intro η hη hle μt hμt
    haveI := hμt.1
    have hle1 : η ≤ ηℓ := hle.trans (min_le_left _ _)
    have hle2 : η ≤ ηs := hle.trans (min_le_right _ _)
    obtain ⟨hγ1, hdr⟩ := hA4 η hη hle1
    obtain ⟨hgap, hKle⟩ := hsm η hη hle2
    set γ := Real.exp (-c₁ * η) + Ct * η ^ (3 / 2 : ℝ)
    set K := cℓ / c₁ * (1 - Real.exp (-c₁ * η)) + Ct * η ^ (3 / 2 : ℝ)
    have hγ0 : 0 ≤ γ := by positivity
    have hK0 : 0 ≤ K := by
      have : 0 ≤ 1 - Real.exp (-c₁ * η) := by
        rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
      positivity
    have hWc : Continuous (fun y => V y ^ ℓ) := hVc.pow ℓ
    have hbound := inv_bound M (fun y => V y ^ ℓ) hWc (fun x => pow_nonneg (hV0 x) ℓ) γ K hγ0 hγ1
      hK0 hdr μt hμt
    have hratio : K / (1 - γ) ≤ 4 * cℓ / c₁ + 1 := by
      have hpos : 0 < c₁ * η / 4 := by positivity
      rw [div_le_iff₀ (by linarith)]
      have : (4 * cℓ / c₁ + 1) * (c₁ * η / 4) = (cℓ + c₁ / 4) * η := by field_simp
      have h2 : (4 * cℓ / c₁ + 1) * (c₁ * η / 4) ≤ (4 * cℓ / c₁ + 1) * (1 - γ) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      linarith
    calc ∫⁻ x, ‖x‖ₑ ^ ℓ ∂μt ≤ ∫⁻ x, (1 + ENNReal.ofReal ((1 / a) ^ ℓ) *
          ENNReal.ofReal (V x ^ ℓ)) ∂μt := by
          refine lintegral_mono (fun x => ?_)
          have := norm_pow_le a ha V (fun y => (hVq y).1) ℓ x
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by have := hV0 x; positivity)]
          exact ENNReal.ofReal_le_ofReal this
      _ = 1 + ENNReal.ofReal ((1 / a) ^ ℓ) * ∫⁻ x, ENNReal.ofReal (V x ^ ℓ) ∂μt := by
          rw [lintegral_add_left measurable_const,
            lintegral_const_mul _ (hWc.measurable.ennreal_ofReal)]
          simp
      _ ≤ 1 + ENNReal.ofReal ((1 / a) ^ ℓ) * ENNReal.ofReal (4 * cℓ / c₁ + 1) := by
          gcongr
          exact hbound.trans (ENNReal.ofReal_le_ofReal hratio)
      _ = ENNReal.ofReal (1 + (1 / a) ^ ℓ * (4 * cℓ / c₁ + 1)) := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (by positivity)]
