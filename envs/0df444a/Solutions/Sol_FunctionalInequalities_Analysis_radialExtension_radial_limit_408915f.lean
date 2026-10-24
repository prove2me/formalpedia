-- Prove2me | solution 1 for FunctionalInequalities.Analysis.radialExtension_radial_limit_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:29:08.623908+00:00
-- url     : https://prove2.me/submissions/a7ce2b70-dad0-4a9d-8cea-6a92ac99991c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Set Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section NormedSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.smul_mem_of_mem_closure
    {K : Set E} (hK : IsOpen K) (hconv : Convex ℝ K) (h0K : (0 : E) ∈ K)
    {x : E} (hx : x ∈ closure K) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t • x ∈ K := by
  have hz : (0 : E) ∈ interior K := by rwa [hK.interior_eq]
  have h := hconv.combo_interior_closure_mem_interior hz hx
    (show 0 < 1 - t by linarith) ht0 (by ring)
  simpa only [smul_zero, zero_add, hK.interior_eq] using h
private lemma FunctionalInequalities.Analysis.radial_mono
    {K : Set E} (h0K : (0 : E) ∈ K) {g : E → ℝ} (hg : ConvexOn ℝ K g)
    (hnn : ∀ y ∈ K, 0 ≤ g y) (hg0 : g 0 = 0) {x : E} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) (htK : t • x ∈ K) :
    g (s • x) ≤ g (t • x) := by
  have ha : 0 ≤ s / t := div_nonneg hs ht.le
  have ha1 : s / t ≤ 1 := (div_le_iff₀ ht).mpr (by simpa using hst)
  have h := hg.2 htK h0K ha (sub_nonneg.mpr ha1) (show s / t + (1 - s / t) = 1 by ring)
  have he : (s / t) • (t • x) + (1 - s / t) • (0 : E) = s • x := by
    rw [smul_zero, add_zero, smul_smul, div_mul_cancel₀ _ ht.ne']
  rw [he, hg0, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at h
  exact h.trans (mul_le_of_le_one_left (hnn _ htK) ha1)
private theorem FunctionalInequalities.Analysis.radialScale_pos (n : ℕ) : 0 < FunctionalInequalities.Analysis.radialScale n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 < (n : ℝ) + 2 := by linarith
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
  dsimp [FunctionalInequalities.Analysis.radialScale]
  simp only [one_div_one] at h
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_lt_one (n : ℕ) : FunctionalInequalities.Analysis.radialScale n < 1 := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have h := one_div_pos.mpr hden
  dsimp [FunctionalInequalities.Analysis.radialScale]
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_monotone : Monotone FunctionalInequalities.Analysis.radialScale := by
  intro m n hmn
  have hm : 0 < (m : ℝ) + 2 := by positivity
  have hle : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
  have h := one_div_le_one_div_of_le hm hle
  dsimp [FunctionalInequalities.Analysis.radialScale]
  linarith
private theorem FunctionalInequalities.Analysis.radialScale_tendsto : Tendsto FunctionalInequalities.Analysis.radialScale atTop (nhds (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds (0 : ℝ)) := by
    have h₀ : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h₂ := (tendsto_add_atTop_iff_nat 2).2 h₀
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h₂
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (nhds (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
private lemma FunctionalInequalities.Analysis.radialExtension_eq_on
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0)
    {x : E} (hx : x ∈ K) : FunctionalInequalities.Analysis.radialExtension K g x = (g x : EReal) := by
  have hmem (n : ℕ) : FunctionalInequalities.Analysis.radialScale n • x ∈ K :=
    smul_mem_of_mem_closure hK hg.1 h0K (subset_closure hx)
      (radialScale_pos n).le (radialScale_lt_one n)
  have hmono : Monotone (fun n => (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal)) := by
    intro m n hmn
    exact EReal.coe_le_coe_iff.mpr
      (radial_mono h0K hg hnn hg0 (radialScale_pos m).le
        (radialScale_monotone hmn) (radialScale_pos n) (hmem n))
  have hcont : ContinuousAt g x := (hg.continuousOn hK).continuousAt (hK.mem_nhds hx)
  have htx : Tendsto (fun n => FunctionalInequalities.Analysis.radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hlim : Tendsto (fun n => (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal)) atTop
      (nhds (g x : EReal)) := EReal.tendsto_coe.mpr (hcont.tendsto.comp htx)
  have he : FunctionalInequalities.Analysis.radialExtension K g x = ⨆ n, (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal) := by
    simp only [FunctionalInequalities.Analysis.radialExtension, FunctionalInequalities.Analysis.radialCut, if_pos (hmem _)]
  rw [he]
  exact iSup_eq_of_tendsto hmono hlim
private lemma FunctionalInequalities.Analysis.radialExtension_eq_top_off
    {K : Set E} {g : E → ℝ} {x : E} (hx : x ∉ closure K) :
    FunctionalInequalities.Analysis.radialExtension K g x = ⊤ := by
  classical
  have htx : Tendsto (fun n => FunctionalInequalities.Analysis.radialScale n • x) atTop (nhds x) := by
    simpa only [one_smul] using radialScale_tendsto.smul (tendsto_const_nhds (x := x))
  have hevent : ∀ᶠ n in atTop, FunctionalInequalities.Analysis.radialScale n • x ∉ closure K :=
    htx.eventually (isClosed_closure.isOpen_compl.mem_nhds hx)
  obtain ⟨n, hn⟩ := hevent.exists
  have hnot : FunctionalInequalities.Analysis.radialScale n • x ∉ K := fun h => hn (subset_closure h)
  apply top_unique
  have h : FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x ≤ FunctionalInequalities.Analysis.radialExtension K g x := le_iSup (fun n => FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x) n
  simpa [FunctionalInequalities.Analysis.radialCut, hnot] using h
section FiniteDimensional
variable [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) (x : E) :
    Tendsto (fun t : ℝ => FunctionalInequalities.Analysis.radialExtension K g (t • x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (FunctionalInequalities.Analysis.radialExtension K g x)) := by
  classical
  by_cases hx : x ∈ closure K
  · have hmem (n : ℕ) : FunctionalInequalities.Analysis.radialScale n • x ∈ K :=
      smul_mem_of_mem_closure hK hg.1 h0K hx (radialScale_pos n).le (radialScale_lt_one n)
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have ha' : a < ⨆ n, FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x := ha
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp ha'
      have hn' : a < (g (FunctionalInequalities.Analysis.radialScale n • x) : EReal) := by
        simpa only [FunctionalInequalities.Analysis.radialCut, if_pos (hmem n)] using hn
      have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), FunctionalInequalities.Analysis.radialScale n < t :=
        nhdsWithin_le_nhds (eventually_gt_nhds (radialScale_lt_one n))
      filter_upwards [hevent, self_mem_nhdsWithin] with t ht ht1
      have ht0 : 0 < t := (radialScale_pos n).trans ht
      have htK : t • x ∈ K := smul_mem_of_mem_closure hK hg.1 h0K hx ht0.le ht1
      rw [radialExtension_eq_on hK h0K hg hnn hg0 htK]
      exact hn'.trans_le (EReal.coe_le_coe_iff.mpr
        (radial_mono h0K hg hnn hg0 (radialScale_pos n).le ht.le ht0 htK))
    · intro a ha
      have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), (0 : ℝ) < t :=
        nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hevent, self_mem_nhdsWithin] with t ht0 ht1
      have htK : t • x ∈ K := smul_mem_of_mem_closure hK hg.1 h0K hx ht0.le ht1
      have hle : FunctionalInequalities.Analysis.radialExtension K g (t • x) ≤ FunctionalInequalities.Analysis.radialExtension K g x := by
        apply iSup_le
        intro n
        have hmtK : FunctionalInequalities.Analysis.radialScale n • (t • x) ∈ K :=
          smul_mem_of_mem_closure hK hg.1 h0K (subset_closure htK)
            (radialScale_pos n).le (radialScale_lt_one n)
        have hprod : FunctionalInequalities.Analysis.radialScale n * t ≤ FunctionalInequalities.Analysis.radialScale n :=
          mul_le_of_le_one_right (radialScale_pos n).le ht1.le
        have hg_le := radial_mono h0K hg hnn hg0
          (mul_nonneg (radialScale_pos n).le ht0.le) hprod (radialScale_pos n) (hmem n)
        have hcut : FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) (t • x) ≤
            FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x := by
          simp only [FunctionalInequalities.Analysis.radialCut, if_pos hmtK, if_pos (hmem n)]
          rw [smul_smul]
          exact EReal.coe_le_coe_iff.mpr hg_le
        exact hcut.trans (le_iSup (fun n => FunctionalInequalities.Analysis.radialCut K g (FunctionalInequalities.Analysis.radialScale n) x) n)
      exact hle.trans_lt ha
  · rw [radialExtension_eq_top_off hx]
    have htx : Tendsto (fun t : ℝ => t • x) (nhdsWithin 1 (Set.Iio 1)) (nhds x) := by
      have h : Tendsto (fun t : ℝ => t • x) (nhds (1 : ℝ)) (nhds ((1 : ℝ) • x)) :=
        (continuous_id.smul continuous_const).continuousAt.tendsto
      simpa only [one_smul] using h.mono_left nhdsWithin_le_nhds
    have hevent : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), t • x ∉ closure K :=
      htx.eventually (isClosed_closure.isOpen_compl.mem_nhds hx)
    apply (tendsto_const_nhds (x := (⊤ : EReal))).congr'
    filter_upwards [hevent] with t ht
    exact (radialExtension_eq_top_off ht).symm
