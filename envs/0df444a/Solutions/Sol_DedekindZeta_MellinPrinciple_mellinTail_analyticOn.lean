-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.mellinTail_analyticOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:24:34.057632+00:00
-- url     : https://prove2.me/submissions/999a4c76-9116-4736-93d5-99b80a97c3a1

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_isBigO_atTop
import Theorems.Thm_DedekindZeta_MellinPrinciple_IsMellinPair_swap
section
open MeasureTheory Set Filter Asymptotics Topology Complex
namespace DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
private theorem mellinTail_summand_aux (φ : ℝ → ℂ)
    (hcont : ContinuousOn φ (Set.Ioi (0 : ℝ)))
    (hdecay : ∀ a : ℝ, φ =O[atTop] fun y : ℝ => y ^ (-a)) (s : ℂ) :
    DifferentiableAt ℂ (mellin ((Ioi 1).indicator φ)) s ∧
      IntegrableOn (fun y : ℝ => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) ∧
      mellin ((Ioi 1).indicator φ) s = ∫ y in Ioi 1, φ y * (y : ℂ) ^ (s - 1) := by
  set ψ : ℝ → ℂ := (Ioi 1).indicator φ with hψ
  -- `φ` is `LocallyIntegrableOn (Ioi 0)`; its restriction to `Ioi 1` (an `Ioi 0`
  -- measurable subset) keeps local integrability, computed compact-subset-wise.
  have hloc : LocallyIntegrableOn ψ (Ioi 0) := by
    rw [hψ, locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hKsub hKcomp
    exact ((hcont.locallyIntegrableOn measurableSet_Ioi).integrableOn_compact_subset
      hKsub hKcomp).indicator measurableSet_Ioi
  -- `ψ = φ` eventually at `∞`, so it inherits the super-polynomial decay.
  have heqtop : φ =ᶠ[atTop] ψ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have : y ∈ Ioi (1 : ℝ) := hy
    simp [hψ, Set.indicator_of_mem this]
  have htop : ψ =O[atTop] fun y : ℝ => y ^ (-(s.re + 1)) :=
    (hdecay (s.re + 1)).congr' heqtop (EventuallyEq.refl _ _)
  -- `ψ = 0` near `0`, so it is `O(y^{-b})` for every `b`.
  have h01 : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (by norm_num [Set.mem_Iio]))
  have heqbot : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] ψ := by
    filter_upwards [h01] with y hy
    have hy' : y ∉ Ioi (1 : ℝ) := by
      simp only [Set.mem_Ioi, not_lt]; exact le_of_lt hy
    simp [hψ, Set.indicator_of_notMem hy']
  have hbot : ψ =O[𝓝[>] (0 : ℝ)] fun y : ℝ => y ^ (-(s.re - 1)) :=
    (isBigO_zero _ _).congr' heqbot (EventuallyEq.refl _ _)
  have hdiff : DifferentiableAt ℂ (mellin ψ) s :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)
  have hconv' : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • ψ y) (Ioi 0) :=
    mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hEq : EqOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • ψ y)
      (fun y => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) := by
    intro y hy
    simp only [hψ, Set.indicator_of_mem hy, smul_eq_mul]
    ring
  have hinteg : IntegrableOn (fun y : ℝ => φ y * (y : ℂ) ^ (s - 1)) (Ioi 1) :=
    (IntegrableOn.mono_set hconv' hsub).congr_fun hEq measurableSet_Ioi
  have hval : mellin ψ s = ∫ y in Ioi 1, φ y * (y : ℂ) ^ (s - 1) := by
    have hpt : ∀ y : ℝ, (y : ℂ) ^ (s - 1) • ψ y
        = (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • φ t) y := by
      intro y
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · rw [hψ, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      · rw [hψ, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
    unfold mellin
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [smul_eq_mul, mul_comm]
  exact ⟨hdiff, hinteg, hval⟩
end DedekindZeta.MellinPrinciple
end

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) :
    AnalyticOnNhd ℂ (mellinTail f g a₀ b₀ C k) Set.univ := by
  have Pf := fun s : ℂ => mellinTail_summand_aux (fun y : ℝ => f y - a₀)
    (h.hf_cont.sub continuousOn_const) (fun a => reducedMellin_isBigO_atTop h a) s
  have Pg := fun s : ℂ => mellinTail_summand_aux (fun y : ℝ => g y - b₀)
    (h.hg_cont.sub continuousOn_const) (fun a => reducedMellin_isBigO_atTop h.swap a) s
  -- `mellinTail` is, pointwise, the sum of two entire (translated) Mellin tails.
  have hfun : mellinTail f g a₀ b₀ C k
      = fun s => mellin ((Ioi 1).indicator (fun y : ℝ => f y - a₀)) s
          + C * mellin ((Ioi 1).indicator (fun y : ℝ => g y - b₀)) ((k : ℂ) - s) := by
    funext s
    have iA' := (Pf s).2.1
    have iB' := ((Pg ((k : ℂ) - s)).2.1).const_mul C
    unfold mellinTail
    rw [(Pf s).2.2, (Pg ((k : ℂ) - s)).2.2, ← integral_const_mul C,
      ← integral_add iA' iB']
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    beta_reduce
    ring
  rw [hfun, analyticOnNhd_univ_iff_differentiable]
  intro s
  have d1 : DifferentiableAt ℂ
      (fun s : ℂ => mellin ((Ioi 1).indicator (fun y : ℝ => f y - a₀)) s) s := (Pf s).1
  have hinner : DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) - s) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have d2 : DifferentiableAt ℂ
      (fun s : ℂ => mellin ((Ioi 1).indicator (fun y : ℝ => g y - b₀)) ((k : ℂ) - s)) s :=
    ((Pg ((k : ℂ) - s)).1).comp s hinner
  exact d1.add (d2.const_mul C)
end DedekindZeta.MellinPrinciple
