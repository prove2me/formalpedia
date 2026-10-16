-- Prove2me | solution 1 for CauchyRiemannIndex.exists_subseq_cauchy_of_support_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:54:59.133967+00:00
-- url     : https://prove2.me/submissions/0f1c0eca-042e-4259-9051-df730e3fa873

import Mathlib
import Theorems.Thm_CauchyRiemannIndex_eLpNorm_translate_sub_le
import Theorems.Thm_HunterPDE_Compactness_kolmogorov_riesz

-- ===== Scratch/CRRelB.lean =====
/-!
# A common `Lᵖ`-Cauchy subsequence for `W^{1,p}`-bounded `C¹` families with bounded support

Each component family has compact closure in `Lᵖ(ℝᵐ)` (Kolmogorov–Riesz: bounded, tight since the
support is in a fixed ball, equicontinuous by the translation bound); the product of the closures
is compact, so one subsequence converges in every component.
-/

namespace CauchyRiemannIndex

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {m : ℕ}

lemma crrb_memLp (p : ℝ≥0∞) (M : ℝ≥0) {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Continuous f)
    (hb : eLpNorm f p volume ≤ M) : MemLp f p volume :=
  ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hb ENNReal.coe_lt_top⟩

theorem crrb_main {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (r : ℝ) (M : ℝ≥0)
    (g : ℕ → ι → EuclideanSpace ℝ (Fin m) → ℝ) (hg : ∀ k i, ContDiff ℝ 1 (g k i))
    (hsupp : ∀ k i x, r < ‖x‖ → g k i x = 0)
    (hb : ∀ k i, eLpNorm (g k i) p volume ≤ M)
    (hdb : ∀ k i, eLpNorm (fun x => ‖fderiv ℝ (g k i) x‖) p volume ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N,
      eLpNorm (g (φ a) i - g (φ b) i) p volume < ε := by
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  have hmem : ∀ k i, MemLp (g k i) p volume := fun k i =>
    crrb_memLp p M (hg k i).continuous (hb k i)
  set f : ℕ → ι → Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
    fun k i => (hmem k i).toLp (g k i) with hf
  have hcoe : ∀ k i, (f k i : EuclideanSpace ℝ (Fin m) → ℝ) =ᵐ[volume] g k i :=
    fun k i => (hmem k i).coeFn_toLp
  -- each component family is precompact
  have hK : ∀ i, IsCompact (closure (range fun k => f k i)) := by
    intro i
    refine (HunterPDE.Compactness.kolmogorov_riesz p hp' _).2 ⟨?_, ?_, ?_⟩
    · refine ⟨M, ?_⟩
      rintro _ ⟨k, rfl⟩
      rw [Lp.norm_toLp]
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hb k i)
      simpa using this
    · intro ε hε
      refine ⟨r, ?_⟩
      rintro _ ⟨k, rfl⟩
      have hz : (f k i : EuclideanSpace ℝ (Fin m) → ℝ) =ᵐ[volume.restrict {x | r < ‖x‖}] 0 := by
        have h1 := ae_restrict_of_ae (s := {x : EuclideanSpace ℝ (Fin m) | r < ‖x‖}) (hcoe k i)
        have h2 : g k i =ᵐ[volume.restrict {x : EuclideanSpace ℝ (Fin m) | r < ‖x‖}] 0 :=
          ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_norm)
            (fun x hx => hsupp k i x hx)
        filter_upwards [h1, h2] with x hx1 hx2
        rw [hx1, hx2]
      rw [eLpNorm_congr_ae hz, eLpNorm_zero]
      exact ENNReal.ofReal_pos.2 hε
    · intro ε hε
      refine ⟨ε / (M + 1), by positivity, ?_⟩
      rintro h hh _ ⟨k, rfl⟩
      have hsh : (fun x => (f k i : EuclideanSpace ℝ (Fin m) → ℝ) (x + h) -
          (f k i : EuclideanSpace ℝ (Fin m) → ℝ) x) =ᵐ[volume] fun x => g k i (x + h) - g k i x := by
        have h1 := (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin m)))
          h).quasiMeasurePreserving.ae_eq (hcoe k i)
        filter_upwards [h1, hcoe k i] with x hx1 hx2
        simp only [Function.comp_apply] at hx1
        rw [hx1, hx2]
      rw [eLpNorm_congr_ae hsh]
      refine lt_of_le_of_lt (eLpNorm_translate_sub_le p hp hp' (g k i) (hg k i) h) ?_
      have hM0 : (0 : ℝ) ≤ M := M.2
      calc ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ (g k i) x‖) p volume
          ≤ ENNReal.ofReal ‖h‖ * ENNReal.ofReal (M : ℝ) := by
            gcongr
            rw [ENNReal.ofReal_coe_nnreal]; exact hdb k i
        _ = ENNReal.ofReal (‖h‖ * M) := (ENNReal.ofReal_mul (norm_nonneg _)).symm
        _ < ENNReal.ofReal ε := by
            rw [ENNReal.ofReal_lt_ofReal_iff hε]
            have h1 : ‖h‖ * M ≤ ε / (M + 1) * M :=
              mul_le_mul_of_nonneg_right hh.le hM0
            have h2 : ε / (M + 1) * M < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith
            linarith
  -- one subsequence for all components
  have hKpi : IsCompact (Set.pi univ fun i => closure (range fun k => f k i)) :=
    isCompact_univ_pi hK
  have hmemK : ∀ k, f k ∈ Set.pi univ fun i => closure (range fun k => f k i) :=
    fun k i _ => subset_closure ⟨k, rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hKpi.tendsto_subseq hmemK
  refine ⟨φ, hφ, fun i ε hε => ?_⟩
  have hi : Tendsto (fun k => f (φ k) i) atTop (𝓝 (a i)) := tendsto_pi_nhds.1 hlim i
  obtain ⟨N, hN⟩ := (EMetric.cauchySeq_iff.1 hi.cauchySeq) ε hε
  refine ⟨N, fun a' ha b hb' => ?_⟩
  have := hN a' ha b hb'
  rw [Lp.edist_def] at this
  have hsub : ((f (φ a') i : EuclideanSpace ℝ (Fin m) → ℝ) -
      (f (φ b) i : EuclideanSpace ℝ (Fin m) → ℝ)) =ᵐ[volume]
      g (φ a') i - g (φ b) i := (hcoe _ i).sub (hcoe _ i)
  rwa [eLpNorm_congr_ae hsub] at this

end CauchyRiemannIndex

-- ===== Scratch/CRRelBSol.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal NNReal

theorem solution {m : ℕ} {ι : Type*} [Fintype ι]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (r : ℝ) (M : ℝ≥0)
    (g : ℕ → ι → EuclideanSpace ℝ (Fin m) → ℝ) (hg : ∀ k i, ContDiff ℝ 1 (g k i))
    (hsupp : ∀ k i x, r < ‖x‖ → g k i x = 0)
    (hb : ∀ k i, eLpNorm (g k i) p volume ≤ M)
    (hdb : ∀ k i, eLpNorm (fun x => ‖fderiv ℝ (g k i) x‖) p volume ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N,
      eLpNorm (g (φ a) i - g (φ b) i) p volume < ε :=
  crrb_main p hp hp' r M g hg hsupp hb hdb
