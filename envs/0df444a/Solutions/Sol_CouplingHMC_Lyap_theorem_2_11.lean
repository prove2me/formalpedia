-- Prove2me | solution 1 for CouplingHMC.Lyap.theorem_2_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T16:36:12.887992+00:00
-- url     : https://prove2.me/submissions/5f9a212c-66c4-4815-b07f-bf4d8f59c869

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_CouplingHMC_Lyap_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CouplingHMC.Lyap.T211Aux

lemma iter_succ_right {S : Type*} [MetricSpace S] [MeasurableSpace S] (π : Kernel S S) (n : ℕ) :
    iterKernel π (n + 1) = iterKernel π n ∘ₖ π := by
  induction n with
  | zero => simp [iterKernel]
  | succ n ih =>
    show π ∘ₖ iterKernel π (n + 1) = (π ∘ₖ iterKernel π n) ∘ₖ π
    rw [ih, Kernel.comp_assoc]

lemma iter_markov {S : Type*} [MetricSpace S] [MeasurableSpace S] (π : Kernel S S)
    [IsMarkovKernel π] (n : ℕ) : IsMarkovKernel (iterKernel π n) := by
  induction n with
  | zero => show IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    haveI := ih
    show IsMarkovKernel (π ∘ₖ iterKernel π n); infer_instance

/-- iterate of a coupling kernel, composed on the right (first step first) -/
noncomputable def Lk {S : Type*} [MeasurableSpace S] (K : Kernel (S × S) (S × S)) :
    ℕ → Kernel (S × S) (S × S)
  | 0 => Kernel.id
  | n + 1 => Lk K n ∘ₖ K

lemma margL {S : Type*} [MetricSpace S] [MeasurableSpace S] (π : Kernel S S)
    (K : Kernel (S × S) (S × S)) (p : S × S → S) (hp : Measurable p)
    (hK : ∀ z, (K z).map p = π (p z)) :
    ∀ n z, (Lk K n z).map p = iterKernel π n (p z) := by
  intro n
  induction n with
  | zero =>
    intro z
    simp only [Lk, iterKernel, Kernel.id_apply]
    exact Measure.map_dirac' hp z
  | succ n ih =>
    intro z
    ext s hs
    rw [Measure.map_apply hp hs, Lk, Kernel.comp_apply' _ _ _ (hp hs), iter_succ_right,
      Kernel.comp_apply' _ _ _ hs]
    have h1 : ∀ z', Lk K n z' (p ⁻¹' s) = iterKernel π n (p z') s := fun z' => by
      rw [← Measure.map_apply hp hs, ih]
    simp_rw [h1]
    rw [← hK z, lintegral_map (Kernel.measurable_coe _ hs) hp]

lemma phi_bound {S : Type*} [MetricSpace S] [MeasurableSpace S] (K : Kernel (S × S) (S × S))
    (π : Kernel S S) (φ : S → ℝ) (hφm : Measurable φ) (β : ℝ) (hβ : 0 ≤ β)
    (hK1 : ∀ z, (K z).map Prod.fst = π z.1) (hK2 : ∀ z, (K z).map Prod.snd = π z.2)
    (hπφ : ∀ x, ∫⁻ y, ENNReal.ofReal (φ y) ∂(π x) ≤ ENNReal.ofReal (β * φ x)) :
    ∀ n z, ∫⁻ w, (ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2)) ∂(Lk K n z) ≤
      ENNReal.ofReal (β ^ n) * (ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2)) := by
  have hΦ : Measurable (fun w : S × S => ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2)) :=
    ((hφm.comp measurable_fst).ennreal_ofReal).add ((hφm.comp measurable_snd).ennreal_ofReal)
  have step : ∀ z, ∫⁻ w, (ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2)) ∂(K z) ≤
      ENNReal.ofReal β * (ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2)) := by
    intro z
    rw [lintegral_add_left (show Measurable (fun w : S × S => ENNReal.ofReal (φ w.1)) from
      (hφm.comp measurable_fst).ennreal_ofReal)]
    have e1 : ∫⁻ w, ENNReal.ofReal (φ w.1) ∂(K z) = ∫⁻ y, ENNReal.ofReal (φ y) ∂(π z.1) := by
      rw [← hK1 z, lintegral_map hφm.ennreal_ofReal measurable_fst]
    have e2 : ∫⁻ w, ENNReal.ofReal (φ w.2) ∂(K z) = ∫⁻ y, ENNReal.ofReal (φ y) ∂(π z.2) := by
      rw [← hK2 z, lintegral_map hφm.ennreal_ofReal measurable_snd]
    rw [e1, e2, mul_add]
    gcongr
    · exact (hπφ z.1).trans (ENNReal.ofReal_mul hβ).le
    · exact (hπφ z.2).trans (ENNReal.ofReal_mul hβ).le
  intro n
  induction n with
  | zero =>
    intro z
    simp only [Lk, Kernel.id_apply, pow_zero, ENNReal.ofReal_one, one_mul]
    rw [lintegral_dirac' _ hΦ]
  | succ n ih =>
    intro z
    rw [Lk, Kernel.lintegral_comp _ _ _ hΦ]
    calc ∫⁻ b, ∫⁻ w, (ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2)) ∂(Lk K n b) ∂(K z)
        ≤ ∫⁻ b, ENNReal.ofReal (β ^ n) * (ENNReal.ofReal (φ b.1) + ENNReal.ofReal (φ b.2))
            ∂(K z) := lintegral_mono (fun b => ih b)
      _ = ENNReal.ofReal (β ^ n) *
            ∫⁻ b, (ENNReal.ofReal (φ b.1) + ENNReal.ofReal (φ b.2)) ∂(K z) :=
          lintegral_const_mul _ hΦ
      _ ≤ ENNReal.ofReal (β ^ n) *
            (ENNReal.ofReal β * (ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2))) := by
          gcongr; exact step z
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hβ n), pow_succ]

lemma main_bound {S : Type*} [MetricSpace S] [MeasurableSpace S] (K : Kernel (S × S) (S × S))
    (π : Kernel S S) (ψ φ : S → ℝ) (hψm : Measurable ψ) (hφm : Measurable φ)
    (hψ : ∀ x, 0 < ψ x) (hφ : ∀ x, 0 < φ x) (C lam β c : ℝ)
    (hC1 : MainLyapunov π ψ C lam) (hC2 : GlobalLyapunov π φ β)
    (hR : Measurable (fun w : S × S => ENNReal.ofReal (dist w.1 w.2)))
    (hK1 : ∀ z, (K z).map Prod.fst = π z.1) (hK2 : ∀ z, (K z).map Prod.snd = π z.2)
    (hcon : ∀ z : S × S, ψ z.1 ≤ C → ψ z.2 ≤ C →
      ∫⁻ w, ENNReal.ofReal (dist w.1 w.2) ∂(K z) ≤ ENNReal.ofReal (Real.exp (-c) * dist z.1 z.2)) :
    ∀ (n : ℕ) (z : S × S), ∫⁻ w, ENNReal.ofReal (dist w.1 w.2) ∂(Lk K n z) ≤
      ENNReal.ofReal (Real.exp (-(c * n))) * ENNReal.ofReal (dist z.1 z.2) +
      ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
        (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
  obtain ⟨hlam, hC1'⟩ := hC1
  obtain ⟨hβ, hC2', hρφ⟩ := hC2
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hΨ : Measurable (fun w : S × S => ENNReal.ofReal (ψ w.1) + ENNReal.ofReal (ψ w.2)) :=
    ((hψm.comp measurable_fst).ennreal_ofReal).add ((hψm.comp measurable_snd).ennreal_ofReal)
  have hpsi_step : ∀ z : S × S, ψ z.1 ≤ C → ψ z.2 ≤ C →
      ∫⁻ w, (ENNReal.ofReal (ψ w.1) + ENNReal.ofReal (ψ w.2)) ∂(K z) ≤
        ENNReal.ofReal lam * (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
    intro z h1 h2
    rw [lintegral_add_left (show Measurable (fun w : S × S => ENNReal.ofReal (ψ w.1)) from
      (hψm.comp measurable_fst).ennreal_ofReal)]
    have e1 : ∫⁻ w, ENNReal.ofReal (ψ w.1) ∂(K z) = ∫⁻ y, ENNReal.ofReal (ψ y) ∂(π z.1) := by
      rw [← hK1 z, lintegral_map hψm.ennreal_ofReal measurable_fst]
    have e2 : ∫⁻ w, ENNReal.ofReal (ψ w.2) ∂(K z) = ∫⁻ y, ENNReal.ofReal (ψ y) ∂(π z.2) := by
      rw [← hK2 z, lintegral_map hψm.ennreal_ofReal measurable_snd]
    rw [e1, e2, mul_add]
    gcongr
    · exact (hC1' z.1 h1).trans (ENNReal.ofReal_mul hlam0.le).le
    · exact (hC1' z.2 h2).trans (ENNReal.ofReal_mul hlam0.le).le
  have hΦ := phi_bound K π φ hφm β hβ0 hK1 hK2 hC2'
  have hout : ∀ z : S × S, (C < ψ z.1 ∨ C < ψ z.2) →
      ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2) ≤
        deltaC ψ φ C * (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
    intro z hz
    have hs : 0 < ψ z.1 + ψ z.2 := add_pos (hψ _) (hψ _)
    have hD : ENNReal.ofReal ((φ z.1 + φ z.2) / (ψ z.1 + ψ z.2)) ≤ deltaC ψ φ C :=
      le_iSup_of_le z.1 (le_iSup_of_le z.2 (le_iSup_of_le hz le_rfl))
    calc ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2)
        = ENNReal.ofReal ((φ z.1 + φ z.2) / (ψ z.1 + ψ z.2)) *
            (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
          rw [← ENNReal.ofReal_add (hψ _).le (hψ _).le,
            ← ENNReal.ofReal_mul (div_nonneg (add_pos (hφ _) (hφ _)).le hs.le),
            div_mul_cancel₀ _ hs.ne', ENNReal.ofReal_add (hφ _).le (hφ _).le]
      _ ≤ _ := by gcongr
  have hRΦ : ∀ w : S × S, ENNReal.ofReal (dist w.1 w.2) ≤
      ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2) := fun w => by
    rw [← ENNReal.ofReal_add (hφ _).le (hφ _).le]
    exact ENNReal.ofReal_le_ofReal (hρφ _ _)
  have ha : ∀ n : ℕ, 0 ≤ β ^ n * lam ^ ((n : ℤ) - 1) := fun n =>
    mul_nonneg (pow_nonneg hβ0 n) (zpow_nonneg hlam0.le _)
  have e2 : ∀ n : ℕ, lam ^ (((n + 1 : ℕ) : ℤ) - 1) = lam ^ n := by
    intro n; push_cast; rw [add_sub_cancel_right, zpow_natCast]
  have hcoef : ∀ n : ℕ, β ^ n * lam ^ ((n : ℤ) - 1) * lam ≤
      β ^ (n + 1) * lam ^ (((n + 1 : ℕ) : ℤ) - 1) := by
    intro n
    have e1 : lam ^ ((n : ℤ) - 1) * lam = lam ^ n := by
      rw [zpow_sub_one₀ hlam0.ne', inv_mul_cancel_right₀ hlam0.ne', zpow_natCast]
    rw [mul_assoc, e1, e2]
    have h3 : 0 ≤ lam ^ n := pow_nonneg hlam0.le n
    have h4 : β ^ n ≤ β ^ (n + 1) := pow_le_pow_right₀ hβ (Nat.le_succ n)
    nlinarith
  have hcoefB : ∀ n : ℕ, β ^ (n + 1) ≤ β ^ (n + 1) * lam ^ (((n + 1 : ℕ) : ℤ) - 1) := by
    intro n
    rw [e2]
    exact le_mul_of_one_le_right (pow_nonneg hβ0 _) (one_le_pow₀ hlam)
  intro n
  induction n with
  | zero =>
    intro z
    simp only [Lk, Kernel.id_apply]
    rw [lintegral_dirac' _ hR]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_self_add
  | succ n ih =>
    intro z
    by_cases hA : ψ z.1 ≤ C ∧ ψ z.2 ≤ C
    · rw [Lk, Kernel.lintegral_comp _ _ _ hR]
      calc ∫⁻ b, ∫⁻ w, ENNReal.ofReal (dist w.1 w.2) ∂(Lk K n b) ∂(K z)
          ≤ ∫⁻ b, (ENNReal.ofReal (Real.exp (-(c * n))) * ENNReal.ofReal (dist b.1 b.2) +
            ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
              (ENNReal.ofReal (ψ b.1) + ENNReal.ofReal (ψ b.2))) ∂(K z) :=
            lintegral_mono (fun b => ih b)
        _ = ENNReal.ofReal (Real.exp (-(c * n))) * ∫⁻ b, ENNReal.ofReal (dist b.1 b.2) ∂(K z) +
            ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
              ∫⁻ b, (ENNReal.ofReal (ψ b.1) + ENNReal.ofReal (ψ b.2)) ∂(K z) := by
          rw [lintegral_add_left (hR.const_mul _), lintegral_const_mul _ hR,
            lintegral_const_mul _ hΨ]
        _ ≤ ENNReal.ofReal (Real.exp (-(c * n))) * ENNReal.ofReal (Real.exp (-c) * dist z.1 z.2) +
            ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
              (ENNReal.ofReal lam * (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2))) := by
          gcongr
          · exact hcon z hA.1 hA.2
          · exact hpsi_step z hA.1 hA.2
        _ ≤ _ := by
          gcongr ?_ + ?_
          · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            apply le_of_eq
            congr 1
            rw [show -(c * ((n + 1 : ℕ) : ℝ)) = -(c * n) + -c by push_cast; ring, Real.exp_add]
            ring
          · calc ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
                  (ENNReal.ofReal lam * (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)))
                = ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1) * lam) * deltaC ψ φ C *
                  (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
                  rw [ENNReal.ofReal_mul (ha n)]; ring
              _ ≤ _ := by gcongr ?_ * _ * _; exact ENNReal.ofReal_le_ofReal (hcoef n)
    · have hz : C < ψ z.1 ∨ C < ψ z.2 := by
        by_contra h
        push Not at h
        exact hA h
      calc _ ≤ ∫⁻ w, (ENNReal.ofReal (φ w.1) + ENNReal.ofReal (φ w.2)) ∂(Lk K (n + 1) z) :=
            lintegral_mono hRΦ
        _ ≤ ENNReal.ofReal (β ^ (n + 1)) * (ENNReal.ofReal (φ z.1) + ENNReal.ofReal (φ z.2)) :=
            hΦ (n + 1) z
        _ ≤ ENNReal.ofReal (β ^ (n + 1)) *
              (deltaC ψ φ C * (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2))) := by
            gcongr; exact hout z hz
        _ ≤ ENNReal.ofReal (β ^ (n + 1) * lam ^ (((n + 1 : ℕ) : ℤ) - 1)) * deltaC ψ φ C *
              (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2)) := by
            rw [← mul_assoc]; gcongr; exact hcoefB n
        _ ≤ _ := le_add_self

end CouplingHMC.Lyap.T211Aux

open CouplingHMC.Lyap.T211Aux

open MeasureTheory ProbabilityTheory CouplingHMC.Lyap in
theorem solution {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (π : Kernel S S) [IsMarkovKernel π] (ψ φ : S → ℝ) (hψm : Measurable ψ) (hφm : Measurable φ)
    (hψ : ∀ x, 0 < ψ x) (hφ : ∀ x, 0 < φ x) (C : ℝ) (hC : 0 < C) (lam β c : ℝ)
    (hC1 : MainLyapunov π ψ C lam) (hC2 : GlobalLyapunov π φ β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (XY : S × S × Ω → S × S)
    (hC3 : LocalContractivity π ψ C P XY c)
    (n : ℕ) (ν η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    kantorovich (ν.bind (iterKernel π n)) (η.bind (iterKernel π n)) ≤
      ENNReal.ofReal (Real.exp (-(c * n))) * kantorovich ν η +
        ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) *
          ((∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (ψ x) ∂η) * deltaC ψ φ C := by
  obtain ⟨hP, hXY, hc, hmarg, hloc⟩ := hC3
  haveI := hP
  have hR : Measurable (fun w : S × S => ENNReal.ofReal (dist w.1 w.2)) :=
    continuous_dist.measurable.ennreal_ofReal
  have hΨ : Measurable (fun w : S × S => ENNReal.ofReal (ψ w.1) + ENNReal.ofReal (ψ w.2)) :=
    ((hψm.comp measurable_fst).ennreal_ofReal).add ((hψm.comp measurable_snd).ennreal_ofReal)
  have hf : Measurable (fun q : (S × S) × Ω => XY (q.1.1, q.1.2, q.2)) :=
    hXY.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hmz : ∀ z : S × S, Measurable (fun ω => XY (z.1, z.2, ω)) := fun z =>
    hXY.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  set K : Kernel (S × S) (S × S) :=
    Kernel.map (Kernel.id ×ₖ Kernel.const (S × S) P)
      (fun q : (S × S) × Ω => XY (q.1.1, q.1.2, q.2)) with hKdef
  have hKz : ∀ z : S × S, K z = P.map (fun ω => XY (z.1, z.2, ω)) := by
    intro z
    rw [hKdef, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
    rfl
  have hK1 : ∀ z : S × S, (K z).map Prod.fst = π z.1 := by
    intro z
    rw [hKz, Measure.map_map measurable_fst (hmz z)]
    exact (hmarg z.1 z.2).1
  have hK2 : ∀ z : S × S, (K z).map Prod.snd = π z.2 := by
    intro z
    rw [hKz, Measure.map_map measurable_snd (hmz z)]
    exact (hmarg z.1 z.2).2
  have hcon : ∀ z : S × S, ψ z.1 ≤ C → ψ z.2 ≤ C →
      ∫⁻ w, ENNReal.ofReal (dist w.1 w.2) ∂(K z) ≤
        ENNReal.ofReal (Real.exp (-c) * dist z.1 z.2) := by
    intro z h1 h2
    rw [hKz, lintegral_map hR (hmz z)]
    exact hloc z.1 z.2 h1 h2
  have hmain := main_bound K π ψ φ hψm hφm hψ hφ C lam β c hC1 hC2 hR hK1 hK2 hcon n
  haveI := iter_markov π n
  have hm1 := margL π K Prod.fst measurable_fst hK1 n
  have hm2 := margL π K Prod.snd measurable_snd hK2 n
  have key : ∀ γ ∈ MongeKantorovichYao.transferencePlans ν η,
      kantorovich (ν.bind (iterKernel π n)) (η.bind (iterKernel π n)) ≤
        ENNReal.ofReal (Real.exp (-(c * n))) * ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ +
        ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) *
          ((∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (ψ x) ∂η) *
            deltaC ψ φ C := by
    rintro γ ⟨hγP, hγ1, hγ2⟩
    have hΓ1 : (γ.bind (Lk K n)).map Prod.fst = ν.bind (iterKernel π n) := by
      ext s hs
      rw [Measure.map_apply measurable_fst hs,
        Measure.bind_apply (measurable_fst hs) (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable, ← hγ1,
        lintegral_map (Kernel.measurable_coe _ hs) measurable_fst]
      congr 1
      ext z
      rw [← Measure.map_apply measurable_fst hs, hm1]
    have hΓ2 : (γ.bind (Lk K n)).map Prod.snd = η.bind (iterKernel π n) := by
      ext s hs
      rw [Measure.map_apply measurable_snd hs,
        Measure.bind_apply (measurable_snd hs) (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable, ← hγ2,
        lintegral_map (Kernel.measurable_coe _ hs) measurable_snd]
      congr 1
      ext z
      rw [← Measure.map_apply measurable_snd hs, hm2]
    have hΓP : IsProbabilityMeasure (γ.bind (Lk K n)) := by
      constructor
      have h : ((γ.bind (Lk K n)).map Prod.fst) Set.univ =
          (ν.bind (iterKernel π n)) Set.univ := by rw [hΓ1]
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
      rw [h, Measure.bind_apply MeasurableSet.univ (Kernel.measurable _).aemeasurable]
      simp
    have hmem : γ.bind (Lk K n) ∈ MongeKantorovichYao.transferencePlans
        (ν.bind (iterKernel π n)) (η.bind (iterKernel π n)) := ⟨hΓP, hΓ1, hΓ2⟩
    have hψ1 : ∫⁻ z, ENNReal.ofReal (ψ z.1) ∂γ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := by
      rw [← hγ1, lintegral_map hψm.ennreal_ofReal measurable_fst]
    have hψ2 : ∫⁻ z, ENNReal.ofReal (ψ z.2) ∂γ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂η := by
      rw [← hγ2, lintegral_map hψm.ennreal_ofReal measurable_snd]
    calc kantorovich (ν.bind (iterKernel π n)) (η.bind (iterKernel π n))
        ≤ ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂(γ.bind (Lk K n)) := iInf₂_le _ hmem
      _ = ∫⁻ z, ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂(Lk K n z) ∂γ :=
          Measure.lintegral_bind (Kernel.measurable _).aemeasurable hR.aemeasurable
      _ ≤ ∫⁻ z, (ENNReal.ofReal (Real.exp (-(c * n))) * ENNReal.ofReal (dist z.1 z.2) +
            ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
              (ENNReal.ofReal (ψ z.1) + ENNReal.ofReal (ψ z.2))) ∂γ :=
          lintegral_mono (fun z => hmain z)
      _ = ENNReal.ofReal (Real.exp (-(c * n))) * ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ +
            ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) * deltaC ψ φ C *
              ((∫⁻ z, ENNReal.ofReal (ψ z.1) ∂γ) + ∫⁻ z, ENNReal.ofReal (ψ z.2) ∂γ) := by
          rw [lintegral_add_left (hR.const_mul _), lintegral_const_mul _ hR,
            lintegral_const_mul _ hΨ,
            lintegral_add_left (show Measurable (fun w : S × S => ENNReal.ofReal (ψ w.1)) from
              (hψm.comp measurable_fst).ennreal_ofReal)]
      _ = _ := by rw [hψ1, hψ2]; ring
  have hE0 : ENNReal.ofReal (Real.exp (-(c * n))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hEt : ENNReal.ofReal (Real.exp (-(c * n))) ≠ ∞ := ENNReal.ofReal_ne_top
  calc kantorovich (ν.bind (iterKernel π n)) (η.bind (iterKernel π n))
      ≤ ⨅ γ ∈ MongeKantorovichYao.transferencePlans ν η,
          (ENNReal.ofReal (Real.exp (-(c * n))) * ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ +
          ENNReal.ofReal (β ^ n * lam ^ ((n : ℤ) - 1)) *
            ((∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (ψ x) ∂η) *
              deltaC ψ φ C) := le_iInf₂ key
    _ = _ := by
      unfold kantorovich
      simp_rw [ENNReal.mul_iInf_of_ne hE0 hEt, ENNReal.iInf_add]
