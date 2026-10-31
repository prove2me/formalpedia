-- Prove2me | solution 2 for EquilibriumExperiment.Gradient.proposition_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:43:21.478485+00:00
-- url     : https://prove2.me/submissions/ab6d9c3f-88cb-4bc0-a5d1-40c2c7923f38

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_4_muLim_hasDerivAt
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology

open EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β) :
    HasDerivAt M.u
      (M.muLimDeriv p *
          (M.r (M.d / M.muLim p) - p * M.ω (M.d / M.muLim p) -
            (deriv M.r (M.d / M.muLim p) - p * deriv M.ω (M.d / M.muLim p)) *
              (M.d / M.muLim p)) -
        M.ω (M.d / M.muLim p) * M.muLim p) p := by
  have hM' := hM
  obtain ⟨hd, -, -, -, -, -, hω, -, -, -, -, -, -, -, -, -, -, -, -, -, hr, -⟩ := hM'
  have hωs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M.ω (Set.Ioi 0) := hω.2.1
  -- `μ_a(p) > 0` (existence part of Lemma 2)
  have hex : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β := by
    obtain ⟨μ, ⟨h1, h2⟩, -⟩ := ((lemma_2 M hM).1 p hp hpos).1
    exact ⟨μ, h1, h2⟩
  have hμpos : 0 < M.muLim p := by
    unfold Market.muLim
    rw [dif_pos hex]
    exact hex.choose_spec.1.1
  -- `μ_a` is differentiable at `p` with derivative `μ'_a(p)` (Lemma 4, (3.20))
  have hmu : HasDerivAt M.muLim (M.muLimDeriv p) p := lemma_4_muLim_hasDerivAt M hM hp hpos
  set μ := M.muLim p with hμdef
  set μ' := M.muLimDeriv p with hμ'def
  have hw0 : 0 < M.d / μ := div_pos hd hμpos
  have hopen : Set.Ioi (0 : ℝ) ∈ 𝓝 (M.d / μ) := Ioi_mem_nhds hw0
  have hrd : HasDerivAt M.r (deriv M.r (M.d / μ)) (M.d / μ) :=
    ((hr.differentiableOn (by simp)).differentiableAt hopen).hasDerivAt
  have hωd : HasDerivAt M.ω (deriv M.ω (M.d / μ)) (M.d / μ) :=
    ((hωs.differentiableOn (by simp)).differentiableAt hopen).hasDerivAt
  -- `w(p') = d_a / μ_a(p')`
  have hw : HasDerivAt (fun p' => M.d / M.muLim p') ((0 * μ - M.d * μ') / μ ^ 2) p :=
    (hasDerivAt_const p M.d).div hmu hμpos.ne'
  have h1 : HasDerivAt (fun p' => M.r (M.d / M.muLim p'))
      (deriv M.r (M.d / μ) * ((0 * μ - M.d * μ') / μ ^ 2)) p := hrd.comp p hw
  have h2 : HasDerivAt (fun p' => M.ω (M.d / M.muLim p'))
      (deriv M.ω (M.d / μ) * ((0 * μ - M.d * μ') / μ ^ 2)) p := hωd.comp p hw
  have H : HasDerivAt (fun p' => (M.r (M.d / M.muLim p') - p' * M.ω (M.d / M.muLim p')) *
      M.muLim p')
      ((deriv M.r (M.d / μ) * ((0 * μ - M.d * μ') / μ ^ 2) -
        (1 * M.ω (M.d / μ) + p * (deriv M.ω (M.d / μ) * ((0 * μ - M.d * μ') / μ ^ 2)))) * μ +
        (M.r (M.d / μ) - p * M.ω (M.d / μ)) * μ') p :=
    (h1.sub ((hasDerivAt_id' p).mul h2)).mul hmu
  refine H.congr_deriv ?_
  field_simp
  ring
