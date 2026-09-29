-- Prove2me | solution 1 for CalibratedCE.Convergence.calibrated_best_response_converges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:10:43.878384+00:00
-- url     : https://prove2.me/submissions/a5dad36c-e5c8-44b7-beb8-9ef3e754bca4

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

theorem aux_cbr_empDist_sum {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ)
    (g : Fin m → Fin n → ℝ) :
    ∑ a, ∑ b, empDist x y t a b * g a b = (∑ s ∈ Finset.range t, g (x s) (y s)) / t := by
  unfold empDist
  have h : ∀ a b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) * g a b
      = ∑ s ∈ Finset.range t, if x s = a ∧ y s = b then g a b else 0 := by
    intro a b
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  calc ∑ a, ∑ b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) / t * g a b
      = (∑ a, ∑ b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ)
          * g a b) / t := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = (∑ s ∈ Finset.range t, g (x s) (y s)) / t := by
        congr 1
        simp_rw [h]
        calc (∑ a : Fin m, ∑ b : Fin n, ∑ s ∈ Finset.range t,
              (if x s = a ∧ y s = b then g a b else 0))
            = ∑ a : Fin m, ∑ s ∈ Finset.range t, ∑ b : Fin n,
              (if x s = a ∧ y s = b then g a b else 0) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ s ∈ Finset.range t, ∑ a : Fin m, ∑ b : Fin n,
              (if x s = a ∧ y s = b then g a b else 0) := Finset.sum_comm
          _ = ∑ s ∈ Finset.range t, g (x s) (y s) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.sum_eq_single (x s)]
            · rw [Finset.sum_eq_single (y s)]
              · simp
              · intro b _ hb
                simp [Ne.symm hb]
              · simp
            · intro a _ ha
              refine Finset.sum_eq_zero fun b _ => ?_
              simp [Ne.symm ha]
            · simp

theorem aux_cbr_regret {k l : ℕ} (v : Fin l → Fin k → ℝ) (R : (Fin k → ℝ) → Fin l)
    (hR : ∀ p : Fin k → ℝ, IsDist p → ∀ a' : Fin l, ∑ b, p b * v a' b ≤ ∑ b, p b * v (R p) b)
    (f : ℕ → Fin k → ℝ) (hf : ∀ t, IsDist (f t)) (z : ℕ → Fin k) (Φ : Fin l → Fin l)
    (t : ℕ) :
    (∑ s ∈ Finset.range t, (v (Φ (R (f s))) (z s) - v (R (f s)) (z s))) / t ≤
      (2 * ∑ a, ∑ b, |v a b|) * ∑ j, Shared.calibScore f z j t := by
  set C := ∑ a, ∑ b, |v a b| with hCdef
  have hC : ∀ a b, |v a b| ≤ C := by
    intro a b
    calc |v a b| ≤ ∑ b, |v a b| :=
          Finset.single_le_sum (f := fun b => |v a b|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ b)
      _ ≤ C := Finset.single_le_sum (f := fun a => ∑ b, |v a b|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  clear_value C
  set w : (Fin k → ℝ) → Fin k → ℝ := fun p b => v (Φ (R p)) b - v (R p) b with hw
  have hwC : ∀ p b, |w p b| ≤ 2 * C := by
    intro p b
    simp only [hw]
    calc |v (Φ (R p)) b - v (R p) b| ≤ |v (Φ (R p)) b| + |v (R p) b| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hC (Φ (R p)) b, hC (R p) b]
  set img := (Finset.range t).image f with himg
  -- key inequality
  have key : ∑ s ∈ Finset.range t, (v (Φ (R (f s))) (z s) - v (R (f s)) (z s)) ≤
      ∑ p ∈ img, ∑ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range t) (t := img) (g := f)
      (fun i hi => Finset.mem_image_of_mem f hi)]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨s₀, -, hs₀⟩ := Finset.mem_image.1 hp
    have hpd : IsDist p := hs₀ ▸ hf s₀
    have step1 : ∑ i ∈ Finset.range t with f i = p, (v (Φ (R (f i))) (z i) - v (R (f i)) (z i))
        = ∑ i ∈ Finset.range t with f i = p, w p (z i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.1 hi).2]
    have step2 : ∑ i ∈ Finset.range t with f i = p, w p (z i)
        = ∑ j, (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) * w p j := by
      rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.range t).filter (fun i => f i = p))
        (t := Finset.univ) (g := z) (fun i _ => Finset.mem_univ (z i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_const, Finset.filter_filter, nsmul_eq_mul]
    have step3 : ∀ j, (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
        = Shared.rho f z p j t * (Shared.N f p t : ℝ) := by
      intro j
      unfold Shared.rho
      split_ifs with hN
      · simp only [zero_mul, Nat.cast_eq_zero, Finset.card_eq_zero]
        unfold Shared.N at hN
        rw [Finset.card_eq_zero] at hN
        apply Finset.eq_empty_of_forall_notMem
        intro s hs
        have : s ∈ (Finset.range t).filter (fun s => f s = p) := by
          simp only [Finset.mem_filter] at hs ⊢
          exact ⟨hs.1, hs.2.1⟩
        rw [hN] at this
        simp at this
      · have : (Shared.N f p t : ℝ) ≠ 0 := by exact_mod_cast hN
        field_simp
    rw [step1, step2]
    simp_rw [step3]
    have hbr : ∑ j, p j * w p j ≤ 0 := by
      have := hR p hpd (Φ (R p))
      simp only [hw, mul_sub, Finset.sum_sub_distrib]
      linarith
    have hNnn : (0 : ℝ) ≤ Shared.N f p t := Nat.cast_nonneg _
    calc ∑ j, Shared.rho f z p j t * (Shared.N f p t : ℝ) * w p j
        = ∑ j, (Shared.rho f z p j t - p j) * (Shared.N f p t : ℝ) * w p j
          + (Shared.N f p t : ℝ) * ∑ j, p j * w p j := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ∑ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C) + 0 := by
          refine add_le_add (Finset.sum_le_sum fun j _ => ?_)
            (mul_nonpos_of_nonneg_of_nonpos hNnn hbr)
          calc (Shared.rho f z p j t - p j) * (Shared.N f p t : ℝ) * w p j
                ≤ |(Shared.rho f z p j t - p j) * (Shared.N f p t : ℝ) * w p j| := le_abs_self _
              _ = |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * |w p j| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hNnn]
              _ ≤ |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C) := by
                gcongr
                exact hwC p j
      _ = ∑ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C) := by ring
  calc (∑ s ∈ Finset.range t, (v (Φ (R (f s))) (z s) - v (R (f s)) (z s))) / t
      ≤ (∑ p ∈ img, ∑ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C)) / t :=
        div_le_div_of_nonneg_right key (Nat.cast_nonneg _)
    _ = (2 * C) * ∑ j, Shared.calibScore f z j t := by
        unfold Shared.calibScore
        rw [Finset.sum_comm (s := img) (t := Finset.univ)
          (f := fun p j => |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) * (2 * C)),
          Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

theorem aux_cbr_compact {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (X : ℕ → Fin m → Fin n → ℝ)
    (e₁ e₂ : ℕ → ℝ) (he₁ : Tendsto e₁ atTop (𝓝 0)) (he₂ : Tendsto e₂ atTop (𝓝 0))
    (hnn : ∀ t a b, 0 ≤ X t a b) (hle : ∀ t a b, X t a b ≤ 1)
    (hsum : ∀ t, 1 ≤ t → ∑ a, ∑ b, X t a b = 1)
    (hreg₁ : ∀ t (Φ : Fin m → Fin m),
      ∑ a, ∑ b, X t a b * u₁ (Φ a) b ≤ ∑ a, ∑ b, X t a b * u₁ a b + e₁ t)
    (hreg₂ : ∀ t (Φ : Fin n → Fin n),
      ∑ a, ∑ b, X t a b * u₂ a (Φ b) ≤ ∑ a, ∑ b, X t a b * u₂ a b + e₂ t) :
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin m → Fin n → ℝ, IsCE u₁ u₂ D ∧
      ∀ a b, |X t a b - D a b| ≤ ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hT⟩ := hcon
  choose φ hφ hφD using fun k : ℕ => hT (k + 1)
  have hmem : ∀ k, X (φ k) ∈ Set.Icc (0 : Fin m → Fin n → ℝ) 1 := fun k =>
    ⟨fun a b => hnn _ a b, fun a b => hle _ a b⟩
  obtain ⟨D, -, ψ, hψ, hlim⟩ := (isCompact_Icc).tendsto_subseq hmem
  have hφψ : Tendsto (fun k => φ (ψ k)) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) (hψ.tendsto_atTop)
    have := hφ (ψ k)
    omega
  have hcoord : ∀ a b, Tendsto (fun k => X (φ (ψ k)) a b) atTop (𝓝 (D a b)) := by
    intro a b
    have h1 := tendsto_pi_nhds.1 hlim a
    exact tendsto_pi_nhds.1 h1 b
  have hCE : IsCE u₁ u₂ D := by
    refine ⟨⟨fun a b => ?_, ?_⟩, fun Φ => ?_, fun Φ => ?_⟩
    · exact ge_of_tendsto (hcoord a b) (Eventually.of_forall fun k => hnn _ a b)
    · have h1 : Tendsto (fun k => ∑ a, ∑ b, X (φ (ψ k)) a b) atTop (𝓝 (∑ a, ∑ b, D a b)) :=
        tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => hcoord a b
      have h2 : (fun k => ∑ a, ∑ b, X (φ (ψ k)) a b) = fun _ => (1:ℝ) := by
        funext k
        exact hsum _ (by have := hφ (ψ k); omega)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    · have hL : Tendsto (fun k => ∑ a, ∑ b, X (φ (ψ k)) a b * u₁ a b + e₁ (φ (ψ k))
          - ∑ a, ∑ b, X (φ (ψ k)) a b * u₁ (Φ a) b) atTop
          (𝓝 (∑ a, ∑ b, D a b * u₁ a b + 0 - ∑ a, ∑ b, D a b * u₁ (Φ a) b)) := by
        refine Tendsto.sub (Tendsto.add ?_ (he₁.comp hφψ)) ?_
        · exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
            (hcoord a b).mul_const _
        · exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
            (hcoord a b).mul_const _
      have := ge_of_tendsto hL (Eventually.of_forall fun k => by
        have := hreg₁ (φ (ψ k)) Φ
        show (0:ℝ) ≤ _
        linarith)
      linarith
    · have hL : Tendsto (fun k => ∑ a, ∑ b, X (φ (ψ k)) a b * u₂ a b + e₂ (φ (ψ k))
          - ∑ a, ∑ b, X (φ (ψ k)) a b * u₂ a (Φ b)) atTop
          (𝓝 (∑ a, ∑ b, D a b * u₂ a b + 0 - ∑ a, ∑ b, D a b * u₂ a (Φ b))) := by
        refine Tendsto.sub (Tendsto.add ?_ (he₂.comp hφψ)) ?_
        · exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
            (hcoord a b).mul_const _
        · exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
            (hcoord a b).mul_const _
      have := ge_of_tendsto hL (Eventually.of_forall fun k => by
        have := hreg₂ (φ (ψ k)) Φ
        show (0:ℝ) ≤ _
        linarith)
      linarith
  have hev : ∀ᶠ k in atTop, ∀ a b, |X (φ (ψ k)) a b - D a b| < ε := by
    rw [eventually_all]
    intro a
    rw [eventually_all]
    intro b
    have h := Metric.tendsto_nhds.1 (hcoord a b) ε hε
    filter_upwards [h] with k hk
    rwa [Real.dist_eq] at hk
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨a, b, hab⟩ := hφD (ψ k) D hCE
  linarith [hk a b]

end CalibratedCE.Convergence

open CalibratedCE CalibratedCE.Convergence

theorem solution {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : Shared.Calibrated f₂ (fun s => R₁ (f₁ s))) :
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin m → Fin n → ℝ, IsCE u₁ u₂ D ∧
      ∀ a b, |empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) t a b - D a b| ≤ ε := by
  have he₁ : Tendsto (fun t => (2 * ∑ a, ∑ b, |u₁ a b|) *
      ∑ j, CalibratedCE.Shared.calibScore f₁ (fun s => R₂ (f₂ s)) j t) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ) (fun j _ => hcal₁ j)
    simpa using this.const_mul (2 * ∑ a, ∑ b, |u₁ a b|)
  have he₂ : Tendsto (fun t => (2 * ∑ b, ∑ a, |u₂ a b|) *
      ∑ j, CalibratedCE.Shared.calibScore f₂ (fun s => R₁ (f₁ s)) j t) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ) (fun j _ => hcal₂ j)
    simpa using this.const_mul (2 * ∑ b, ∑ a, |u₂ a b|)
  refine aux_cbr_compact u₁ u₂ (empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s))) _ _ he₁ he₂
    ?_ ?_ ?_ ?_ ?_
  · intro t a b
    unfold empDist
    positivity
  · intro t a b
    unfold empDist
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range t).le
  · intro t ht
    have h := aux_cbr_empDist_sum (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) t (fun _ _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    rw [h]
    have : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    field_simp
  · intro t Φ
    have h := aux_cbr_regret u₁ R₁ hR₁ f₁ hf₁ (fun s => R₂ (f₂ s)) Φ t
    rw [aux_cbr_empDist_sum, aux_cbr_empDist_sum]
    rw [Finset.sum_sub_distrib, sub_div] at h
    linarith
  · intro t Φ
    have h := aux_cbr_regret (fun b a => u₂ a b) R₂ hR₂ f₂ hf₂ (fun s => R₁ (f₁ s)) Φ t
    rw [aux_cbr_empDist_sum, aux_cbr_empDist_sum]
    rw [Finset.sum_sub_distrib, sub_div] at h
    linarith
