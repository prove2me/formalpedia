-- Prove2me | solution 1 for CondPortOT.FiberDual.lp_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:22:58.737898+00:00
-- url     : https://prove2.me/submissions/0c80bafe-d510-43e9-9f19-6d53ec50f60c

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOTLPAux

open CondPortOT.FiberDual

lemma split_sum {N : ℕ} (I : Finset (Fin N)) {M : Type*} [AddCommMonoid M] (f g : Fin N → M) :
    ∑ i ∈ I, f i + ∑ i ∈ Iᶜ, g i = ∑ i, (if i ∈ I then f i else g i) := by
  rw [← Finset.sum_add_sum_compl I (fun i => if i ∈ I then f i else g i)]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  · exact Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.mem_compl.1 hi)]

/-- Weak LP duality. -/
lemma weak_lp {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ) (hε : 0 < ε)
    (lam s : Fin N → ℝ) (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ)
    (hP : ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
            (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
          ((∀ i, 0 ≤ θ i) ∧
            ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t))
    (v : DualPt N) (hv : InV d I ρ v ∧ v.lam = lam ∧ v.s = s) :
    ∑ i, (θ i * lam i + υ i * s i) ≤ v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM := by
  obtain ⟨⟨hυ, hυt, hυ1, ht1, ht2⟩, hθ, hbud⟩ := hP
  obtain ⟨⟨hlam, hnuP, hnuM, hvphi, hpsi, hI, hIc, hsum, hphil⟩, rfl, rfl⟩ := hv
  rw [split_sum I (fun i => θ i + (t - υ i) * d i) (fun i => θ i + υ i * d i)] at hbud
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : 0 ≤ t := le_trans (inv_nonneg.2 hNpos.le) ht1
  set e : Fin N → ℝ := fun i => if i ∈ I then θ i + (t - υ i) * d i else θ i + υ i * d i with he
  have hper : ∀ i, θ i * v.lam i + υ i * v.s i ≤
      v.phi * υ i + t * v.psi i + v.vphi * e i - v.vphi * t * (if i ∈ I then d i else 0) := by
    intro i
    have h1 : θ i * v.lam i ≤ θ i * v.vphi :=
      mul_le_mul_of_nonneg_left (by linarith [hphil i]) (hθ i)
    have h2 : υ i * v.psi i ≤ t * v.psi i := mul_le_mul_of_nonneg_right (hυt i) (hpsi i)
    have hυ0 := (hυ i).1
    simp only [he]
    by_cases hi : i ∈ I
    · rw [if_pos hi, if_pos hi]
      have h3 : υ i * v.s i ≤ υ i * (v.phi - d i * v.vphi + v.psi i) :=
        mul_le_mul_of_nonneg_left (by linarith [hI i hi]) hυ0
      nlinarith
    · rw [if_neg hi, if_neg hi]
      have h3 : υ i * v.s i ≤ υ i * (v.phi + d i * v.vphi + v.psi i) :=
        mul_le_mul_of_nonneg_left (by linarith [hIc i hi]) hυ0
      nlinarith
  have hS := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  have hS' : ∑ i, (θ i * v.lam i + υ i * v.s i) ≤ v.phi * ∑ i, υ i + t * ∑ i, v.psi i +
      v.vphi * (∑ i, e i - t * ∑ i ∈ I, d i) := by
    refine le_trans hS (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  rw [hυ1, mul_one] at hS'
  have hb : v.vphi * (∑ i, e i - t * ∑ i ∈ I, d i) ≤ v.vphi * (N * ρ * t - t * ∑ i ∈ I, d i) :=
    mul_le_mul_of_nonneg_left (by linarith) hvphi
  have hν : t * ∑ i, v.psi i ≤ t * (v.nuP - v.nuM + (∑ i ∈ I, d i - N * ρ) * v.vphi) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0
  have h4 : t * v.nuP ≤ ((N : ℝ) * ε)⁻¹ * v.nuP := mul_le_mul_of_nonneg_right ht2 hnuP
  have h5 : (N : ℝ)⁻¹ * v.nuM ≤ t * v.nuM := mul_le_mul_of_nonneg_right ht1 hnuM
  nlinarith


noncomputable def sg {N : ℕ} (I : Finset (Fin N)) (i : Fin N) : ℝ := if i ∈ I then 1 else -1

/-- The Lagrangian; `x = (υ, t, θ)`, `y = (ϕ, ψ, φ)`. -/
noncomputable def Lag {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (y : ℝ × (Fin N → ℝ) × ℝ) : ℝ :=
  y.1 + ∑ i, (x.2.2 i * (lam i - y.2.2) + x.1 i * (s i - y.1 - y.2.1 i + sg I i * y.2.2 * d i)) +
    x.2.1 * (∑ i, y.2.1 i + y.2.2 * (N * ρ - ∑ i ∈ I, d i))

/-- the Lagrangian as an affine function of the multipliers. -/
lemma Lag_y {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (y : ℝ × (Fin N → ℝ) × ℝ) :
    Lag d I ρ lam s x y = ∑ i, (x.2.2 i * lam i + x.1 i * s i) + y.1 * (1 - ∑ i, x.1 i) +
      ∑ i, y.2.1 i * (x.2.1 - x.1 i) +
      y.2.2 * (-∑ i, x.2.2 i + ∑ i, sg I i * x.1 i * d i + x.2.1 * (N * ρ - ∑ i ∈ I, d i)) := by
  unfold Lag
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_add, mul_sub, add_mul, sub_mul, neg_mul, mul_neg, mul_one]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring


lemma Lag_affine_x {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (y : ℝ × (Fin N → ℝ) × ℝ) (x1 x2 : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (a b : ℝ)
    (hab : a + b = 1) :
    Lag d I ρ lam s (a • x1 + b • x2) y = a * Lag d I ρ lam s x1 y + b * Lag d I ρ lam s x2 y := by
  obtain rfl : b = 1 - a := by linarith
  unfold Lag
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub, add_mul, sub_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

lemma Lag_affine_y {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (y1 y2 : ℝ × (Fin N → ℝ) × ℝ) (a b : ℝ)
    (hab : a + b = 1) :
    Lag d I ρ lam s x (a • y1 + b • y2) = a * Lag d I ρ lam s x y1 + b * Lag d I ρ lam s x y2 := by
  obtain rfl : b = 1 - a := by linarith
  rw [Lag_y, Lag_y, Lag_y]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub, add_mul, sub_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

lemma Lag_cont_x {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (y : ℝ × (Fin N → ℝ) × ℝ) : Continuous fun x => Lag d I ρ lam s x y := by
  unfold Lag; fun_prop

lemma Lag_cont_y {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) : Continuous fun y => Lag d I ρ lam s x y := by
  unfold Lag; fun_prop

/-- the budget constraint in terms of the coefficient of `φ`. -/
lemma budget_iff {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (υ θ : Fin N → ℝ)
    (t : ℝ) :
    (∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t) ↔
      0 ≤ -∑ i, θ i + ∑ i, sg I i * υ i * d i + t * (N * ρ - ∑ i ∈ I, d i) := by
  rw [split_sum I (fun i => θ i + (t - υ i) * d i) (fun i => θ i + υ i * d i)]
  have e : ∑ i, (if i ∈ I then θ i + (t - υ i) * d i else θ i + υ i * d i) =
      ∑ i, θ i + t * ∑ i ∈ I, d i - ∑ i, sg I i * υ i * d i := by
    have hper : ∀ i, (if i ∈ I then θ i + (t - υ i) * d i else θ i + υ i * d i) =
        θ i + t * (if i ∈ I then d i else 0) - sg I i * υ i * d i := by
      intro i; unfold sg; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => hper i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  rw [e]
  constructor <;> intro h <;> nlinarith

lemma g_bound (T n c γ e : ℝ) (hT : n ≤ T) (hn : 0 ≤ n) (he : 0 ≤ e) (hc : c ≤ γ + e) :
    T * max c 0 - n * max (-c) 0 ≤ (if 0 ≤ γ then T * γ else n * γ) + T * e := by
  have hT0 : 0 ≤ T := le_trans hn hT
  rcases le_total 0 c with hc0 | hc0
  · rw [max_eq_left hc0, max_eq_right (by linarith)]
    by_cases hg : 0 ≤ γ
    · rw [if_pos hg]; nlinarith
    · rw [if_neg hg]; push Not at hg; nlinarith
  · rw [max_eq_right hc0, max_eq_left (by linarith)]
    by_cases hg : 0 ≤ γ
    · rw [if_pos hg]; nlinarith
    · rw [if_neg hg]; nlinarith

lemma psi_bound (ψ x β σ δ dd : ℝ) (hσ : σ = 1 ∨ σ = -1) (hδ : 0 ≤ δ)
    (he : x - ψ = β + σ * δ * dd) : max ψ x - ψ ≤ max β 0 + δ * |dd| := by
  have hsg : σ * δ * dd ≤ δ * |dd| := by
    rcases hσ with rfl | rfl
    · nlinarith [le_abs_self dd]
    · nlinarith [neg_abs_le dd]
  rcases le_total ψ x with h | h
  · rw [max_eq_right h]; linarith [le_max_left β 0]
  · rw [max_eq_left h]; linarith [le_max_right β 0, mul_nonneg hδ (abs_nonneg dd)]

lemma Lag_phi {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (a : ℝ) :
    Lag d I ρ lam s x (a, 0, 0) = ∑ i, (x.2.2 i * lam i + x.1 i * s i) + a * (1 - ∑ i, x.1 i) := by
  rw [Lag_y]; simp

lemma Lag_psi {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (ψ : Fin N → ℝ) :
    Lag d I ρ lam s x (0, ψ, 0) = ∑ i, (x.2.2 i * lam i + x.1 i * s i) +
      ∑ i, ψ i * (x.2.1 - x.1 i) := by
  rw [Lag_y]; simp

lemma Lag_vphi {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ : ℝ) (lam s : Fin N → ℝ)
    (x : (Fin N → ℝ) × ℝ × (Fin N → ℝ)) (b : ℝ) :
    Lag d I ρ lam s x (0, 0, b) = ∑ i, (x.2.2 i * lam i + x.1 i * s i) +
      b * (-∑ i, x.2.2 i + ∑ i, sg I i * x.1 i * d i + x.2.1 * (N * ρ - ∑ i ∈ I, d i)) := by
  rw [Lag_y]; simp

end CondPortOTLPAux

open CondPortOTLPAux in
theorem solution {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ)
    (hε : 0 < ε) (lam s : Fin N → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hfeas : ∃ (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ),
      ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
        (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
      ((∀ i, 0 ≤ θ i) ∧
        ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t)) :
    (⨆ (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ)
        (_ : ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
            (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
          ((∀ i, 0 ≤ θ i) ∧
            ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t)),
      ((∑ i, (θ i * lam i + υ i * s i) : ℝ) : EReal)) =
    ⨅ (v : CondPortOT.FiberDual.DualPt N) (_ : CondPortOT.FiberDual.InV d I ρ v ∧ v.lam = lam ∧ v.s = s),
      ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨υ0, t0, θ0, hC0⟩ := hfeas
  set T := ((N : ℝ) * ε)⁻¹ with hT
  have hNT : (N : ℝ)⁻¹ ≤ T := le_trans hC0.1.2.2.2.1 hC0.1.2.2.2.2
  have hT0 : 0 ≤ T := by positivity
  have hNinv0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hNpos.le
  apply le_antisymm
  · refine iSup_le fun υ => iSup_le fun t => iSup_le fun θ => iSup_le fun hC => ?_
    refine le_iInf₂ fun v hv => ?_
    exact EReal.coe_le_coe_iff.2 (weak_lp hN d I ρ ε hε lam s υ t θ hC v hv)
  rw [← EReal.neg_le_neg_iff]
  set K := ∑ i, |d i| + |N * ρ - ∑ i ∈ I, d i| with hK
  have hK0 : 0 ≤ K := by positivity
  set Θ := T * K with hΘ
  have hΘ0 : 0 ≤ Θ := mul_nonneg hT0 hK0
  set X0 : Set ((Fin N → ℝ) × ℝ × (Fin N → ℝ)) := Set.Icc (0 : Fin N → ℝ) (fun _ => T) ×ˢ
    (Set.Icc ((N : ℝ)⁻¹) T ×ˢ Set.Icc (0 : Fin N → ℝ) (fun _ => Θ)) with hX0
  set Y0 : Set (ℝ × (Fin N → ℝ) × ℝ) := Set.univ ×ˢ (Set.Ici (0 : Fin N → ℝ) ×ˢ Set.Ici (0 : ℝ))
    with hY0
  set G : ((Fin N → ℝ) × ℝ × (Fin N → ℝ)) → (ℝ × (Fin N → ℝ) × ℝ) → EReal :=
    fun x y => ((-Lag d I ρ lam s x y : ℝ) : EReal) with hG
  have neX : X0.Nonempty :=
    ⟨(0, (N : ℝ)⁻¹, 0), ⟨le_rfl, fun _ => hT0⟩, ⟨le_rfl, hNT⟩, ⟨le_rfl, fun _ => hΘ0⟩⟩
  have cX : Convex ℝ X0 := (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  have kX : IsCompact X0 := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have cY : Convex ℝ Y0 := convex_univ.prod ((convex_Ici _).prod (convex_Ici _))
  have hmono : Monotone Real.toEReal := fun a b h => EReal.coe_le_coe_iff.2 h
  have hfy : ∀ y ∈ Y0, LowerSemicontinuousOn (fun x => G x y) X0 := fun y _ =>
    (continuous_coe_real_ereal.comp (Lag_cont_x d I ρ lam s y).neg).lowerSemicontinuous.lowerSemicontinuousOn X0
  have hfy' : ∀ y ∈ Y0, QuasiconvexOn ℝ X0 (fun x => G x y) := by
    intro y _
    have hconv : ConvexOn ℝ X0 (fun x => -Lag d I ρ lam s x y) := ⟨cX, fun x1 _ x2 _ a b _ _ hab => by
      simp only [smul_eq_mul]
      rw [Lag_affine_x d I ρ lam s y x1 x2 a b hab]
      linarith⟩
    exact hconv.quasiconvexOn.monotone_comp (g := Real.toEReal) hmono
  have hfx : ∀ x ∈ X0, UpperSemicontinuousOn (fun y => G x y) Y0 := fun x _ =>
    (continuous_coe_real_ereal.comp (Lag_cont_y d I ρ lam s x).neg).upperSemicontinuous.upperSemicontinuousOn Y0
  have hfx' : ∀ x ∈ X0, QuasiconcaveOn ℝ Y0 (fun y => G x y) := by
    intro x _
    have hconc : ConcaveOn ℝ Y0 (fun y => -Lag d I ρ lam s x y) := ⟨cY, fun y1 _ y2 _ a b _ _ hab => by
      simp only [smul_eq_mul]
      rw [Lag_affine_y d I ρ lam s x y1 y2 a b hab]
      linarith⟩
    exact hconc.quasiconcaveOn.monotone_comp (g := Real.toEReal) hmono
  have hmm := Sion.minimax' neX cX kX hfy hfy' cY hfx hfx'
  refine le_trans ?_ (le_trans (le_of_eq hmm) ?_)
  · -- primal side
    refine le_iInf₂ fun x hx => ?_
    obtain ⟨⟨hυ0, hυT⟩, ⟨ht1, htT⟩, ⟨hθ0, hθΘ⟩⟩ := hx
    set O := ∑ i, (x.2.2 i * lam i + x.1 i * s i) with hO
    by_cases hfe : ((∀ i, x.1 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, x.1 i ≤ x.2.1) ∧ ∑ i, x.1 i = 1 ∧
          (N : ℝ)⁻¹ ≤ x.2.1 ∧ x.2.1 ≤ ((N : ℝ) * ε)⁻¹) ∧
        ((∀ i, 0 ≤ x.2.2 i) ∧
          ∑ i ∈ I, (x.2.2 i + (x.2.1 - x.1 i) * d i) + ∑ i ∈ Iᶜ, (x.2.2 i + x.1 i * d i) ≤
            N * ρ * x.2.1)
    · have hobj : ((O : ℝ) : EReal) ≤ ⨆ (υ : Fin N → ℝ) (t : ℝ) (θ : Fin N → ℝ)
          (_ : ((∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, υ i ≤ t) ∧ ∑ i, υ i = 1 ∧
              (N : ℝ)⁻¹ ≤ t ∧ t ≤ ((N : ℝ) * ε)⁻¹) ∧
            ((∀ i, 0 ≤ θ i) ∧
              ∑ i ∈ I, (θ i + (t - υ i) * d i) + ∑ i ∈ Iᶜ, (θ i + υ i * d i) ≤ N * ρ * t)),
          ((∑ i, (θ i * lam i + υ i * s i) : ℝ) : EReal) :=
        le_iSup_of_le x.1 (le_iSup_of_le x.2.1 (le_iSup_of_le x.2.2 (le_iSup_of_le hfe le_rfl)))
      have h0 : (0 : ℝ × (Fin N → ℝ) × ℝ) ∈ Y0 :=
        ⟨Set.mem_univ _, show (0 : Fin N → ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ 0 from le_rfl⟩
      have hL0 : Lag d I ρ lam s x 0 = O := by rw [Lag_y]; simp [hO]
      refine le_trans (EReal.neg_le_neg_iff.2 hobj) (le_iSup₂_of_le 0 h0 (le_of_eq ?_))
      simp only [hG, hL0, EReal.coe_neg]
    · suffices hS : ⨆ y ∈ Y0, G x y = ⊤ by rw [hS]; exact le_top
      rw [EReal.eq_top_iff_forall_lt]
      intro r
      have hex : ∃ y ∈ Y0, Lag d I ρ lam s x y ≤ -(r + 1) := by
        by_cases h1 : ∑ i, x.1 i = 1
        · by_cases h2 : ∀ i, x.1 i ≤ x.2.1
          · have hbud : ¬ (∑ i ∈ I, (x.2.2 i + (x.2.1 - x.1 i) * d i) +
                ∑ i ∈ Iᶜ, (x.2.2 i + x.1 i * d i) ≤ N * ρ * x.2.1) := by
              intro hb
              apply hfe
              refine ⟨⟨fun i => ⟨hυ0 i, ?_⟩, h2, h1, ht1, htT⟩, ⟨fun i => hθ0 i, hb⟩⟩
              rw [← h1]
              exact Finset.single_le_sum (fun j _ => hυ0 j) (Finset.mem_univ i)
            rw [budget_iff] at hbud
            push Not at hbud
            set a3 := -∑ i, x.2.2 i + ∑ i, sg I i * x.1 i * d i + x.2.1 * (N * ρ - ∑ i ∈ I, d i)
              with ha3
            refine ⟨(0, 0, max 0 ((O + r + 1) / (-a3))), ⟨Set.mem_univ _,
              show (0 : Fin N → ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ max 0 _ from le_max_left _ _⟩, ?_⟩
            rw [Lag_vphi, ← ha3, ← hO]
            have hq : (O + r + 1) / (-a3) ≤ max 0 ((O + r + 1) / (-a3)) := le_max_right _ _
            have hq2 : (O + r + 1) / (-a3) * (-a3) = O + r + 1 := div_mul_cancel₀ _ (by linarith)
            have : (O + r + 1) ≤ max 0 ((O + r + 1) / (-a3)) * (-a3) := by
              calc O + r + 1 = (O + r + 1) / (-a3) * (-a3) := hq2.symm
                _ ≤ max 0 ((O + r + 1) / (-a3)) * (-a3) :=
                  mul_le_mul_of_nonneg_right hq (by linarith)
            nlinarith
          · push Not at h2
            obtain ⟨i, hi⟩ := h2
            set c := max 0 ((O + r + 1) / (x.1 i - x.2.1)) with hc
            refine ⟨(0, fun k => if k = i then c else 0, 0),
              ⟨Set.mem_univ _, fun k => by by_cases hk : k = i <;> simp [hk, hc],
                show (0 : ℝ) ≤ 0 from le_rfl⟩, ?_⟩
            rw [Lag_psi, ← hO]
            simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            have hq : (O + r + 1) / (x.1 i - x.2.1) ≤ c := le_max_right _ _
            have hq2 : (O + r + 1) / (x.1 i - x.2.1) * (x.1 i - x.2.1) = O + r + 1 :=
              div_mul_cancel₀ _ (by linarith)
            have : O + r + 1 ≤ c * (x.1 i - x.2.1) := by
              calc O + r + 1 = (O + r + 1) / (x.1 i - x.2.1) * (x.1 i - x.2.1) := hq2.symm
                _ ≤ c * (x.1 i - x.2.1) := mul_le_mul_of_nonneg_right hq (by linarith)
            nlinarith
        · have hne : 1 - ∑ i, x.1 i ≠ 0 := fun h => h1 (by linarith)
          refine ⟨(-(O + r + 1) / (1 - ∑ i, x.1 i), 0, 0), ⟨Set.mem_univ _,
            show (0 : Fin N → ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ 0 from le_rfl⟩, ?_⟩
          rw [Lag_phi, ← hO, div_mul_cancel₀ _ hne]
          linarith
      obtain ⟨y, hy, hLy⟩ := hex
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith : r < r + 1))
        (le_iSup₂_of_le y hy (EReal.coe_le_coe_iff.2 (by linarith)))
  · -- dual side
    refine iSup₂_le fun y hy => ?_
    obtain ⟨-, hψ0, hφ0⟩ := hy
    have hφ0' : 0 ≤ y.2.2 := hφ0
    set ϕ := y.1 with hϕ
    set ψ := y.2.1 with hψ
    set φ := y.2.2 with hφ
    set α : Fin N → ℝ := fun i => lam i - φ with hα
    set β : Fin N → ℝ := fun i => s i - ϕ - ψ i + sg I i * φ * d i with hβ
    set γ := ∑ i, ψ i + φ * (N * ρ - ∑ i ∈ I, d i) with hγ
    set x' : (Fin N → ℝ) × ℝ × (Fin N → ℝ) :=
      (fun i => if 0 < β i then T else 0, if 0 ≤ γ then T else (N : ℝ)⁻¹,
        fun i => if 0 < α i then Θ else 0) with hx'
    have hx'mem : x' ∈ X0 := by
      refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨?_, ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩
      · show (0 : ℝ) ≤ if 0 < β i then T else 0
        split_ifs <;> linarith
      · show (if 0 < β i then T else 0) ≤ T
        split_ifs <;> linarith
      · show (N : ℝ)⁻¹ ≤ if 0 ≤ γ then T else (N : ℝ)⁻¹
        split_ifs <;> linarith
      · show (if 0 ≤ γ then T else (N : ℝ)⁻¹) ≤ T
        split_ifs <;> linarith
      · show (0 : ℝ) ≤ if 0 < α i then Θ else 0
        split_ifs <;> linarith
      · show (if 0 < α i then Θ else 0) ≤ Θ
        split_ifs <;> linarith
    set h := if 0 ≤ γ then T * γ else (N : ℝ)⁻¹ * γ with hh
    have hLx' : Lag d I ρ lam s x' y =
        ϕ + ∑ i, (Θ * max (α i) 0 + T * max (β i) 0) + h := by
      unfold Lag
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hx']
        congr 1
        · by_cases ha : 0 < α i
          · simp only [hα] at ha ⊢; rw [if_pos ha, max_eq_left ha.le]
          · simp only [hα] at ha ⊢; rw [if_neg ha, max_eq_right (not_lt.1 ha)]; ring
        · by_cases hb : 0 < β i
          · simp only [hβ] at hb ⊢; rw [if_pos hb, max_eq_left hb.le]
          · simp only [hβ] at hb ⊢; rw [if_neg hb, max_eq_right (not_lt.1 hb)]; ring
      · simp only [hx', hh]
        split_ifs <;> ring
    -- the repaired dual point
    set δ := ∑ i, max (α i) 0 with hδ
    have hδ0 : 0 ≤ δ := Finset.sum_nonneg fun i _ => le_max_right _ _
    set φ' := φ + δ with hφ'
    set ψ' : Fin N → ℝ := fun i => max (ψ i) (s i + sg I i * φ' * d i - ϕ) with hψ'
    set c' := ∑ i, ψ' i + φ' * (N * ρ - ∑ i ∈ I, d i) with hc'
    let v' : CondPortOT.FiberDual.DualPt N := ⟨lam, s, max c' 0, max (-c') 0, ϕ, φ', ψ'⟩
    have hv' : CondPortOT.FiberDual.InV d I ρ v' ∧ v'.lam = lam ∧ v'.s = s := by
      refine ⟨⟨hlam, le_max_right _ _, le_max_right _ _, by positivity,
        fun i => le_trans (hψ0 i) (le_max_left _ _), fun i hi => ?_, fun i hi => ?_, ?_,
        fun i => ?_⟩, rfl, rfl⟩
      · have := le_max_right (ψ i) (s i + sg I i * φ' * d i - ϕ)
        simp only [v', hψ', sg, if_pos hi, one_mul] at this ⊢
        linarith
      · have := le_max_right (ψ i) (s i + sg I i * φ' * d i - ϕ)
        simp only [v', hψ', sg, if_neg hi] at this ⊢
        linarith
      · simp only [v']
        have : max c' 0 - max (-c') 0 = c' := by
          rcases le_total 0 c' with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        rw [hc'] at this
        linarith
      · simp only [v']
        have h1 : max (α i) 0 ≤ δ :=
          Finset.single_le_sum (f := fun i => max (α i) 0) (fun _ _ => le_max_right _ _)
            (Finset.mem_univ i)
        have h2 : α i ≤ max (α i) 0 := le_max_left _ _
        simp only [hα] at h2
        linarith
    have hobj' : v'.phi + ((N : ℝ) * ε)⁻¹ * v'.nuP - (N : ℝ)⁻¹ * v'.nuM ≤
        Lag d I ρ lam s x' y := by
      rw [hLx']
      simp only [v']
      have hψd : ∀ i, ψ' i - ψ i ≤ max (β i) 0 + δ * |d i| := by
        intro i
        have e : (s i + sg I i * φ' * d i - ϕ) - ψ i = β i + sg I i * δ * d i := by
          simp only [hβ, hφ']; ring
        have hσ : sg I i = 1 ∨ sg I i = -1 := by unfold sg; split_ifs <;> simp
        exact psi_bound (ψ i) _ (β i) (sg I i) δ (d i) hσ hδ0 e
      have hsumψ : ∑ i, ψ' i - ∑ i, ψ i ≤ ∑ i, max (β i) 0 + δ * ∑ i, |d i| := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => hψd i
      have hcγ : c' ≤ γ + (∑ i, max (β i) 0 + δ * K) := by
        have h3 : δ * (N * ρ - ∑ i ∈ I, d i) ≤ δ * |N * ρ - ∑ i ∈ I, d i| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hδ0
        have e1 : c' - γ = (∑ i, ψ' i - ∑ i, ψ i) + δ * (N * ρ - ∑ i ∈ I, d i) := by
          simp only [hc', hγ, hφ']; ring
        have e2 : δ * K = δ * ∑ i, |d i| + δ * |N * ρ - ∑ i ∈ I, d i| := by rw [hK]; ring
        linarith only [e1, e2, hsumψ, h3]
      set e := ∑ i, max (β i) 0 + δ * K with he
      have he0 : 0 ≤ e := by
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_right (β i) 0)
        have := mul_nonneg hδ0 hK0
        linarith only [this, ‹0 ≤ ∑ i, max (β i) 0›]
      have hg : T * max c' 0 - (N : ℝ)⁻¹ * max (-c') 0 ≤ h + T * e :=
        g_bound T (N : ℝ)⁻¹ c' γ e hNT hNinv0 he0 hcγ
      have hΘδ : T * (δ * K) = ∑ i, Θ * max (α i) 0 := by
        rw [← Finset.mul_sum, hΘ, hδ]; ring
      have hsplit : ∑ i, (Θ * max (α i) 0 + T * max (β i) 0) =
          ∑ i, Θ * max (α i) 0 + T * ∑ i, max (β i) 0 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      rw [hsplit, ← hΘδ]
      have hTe : T * e = T * ∑ i, max (β i) 0 + T * (δ * K) := by rw [he, mul_add]
      linarith only [hg, hTe]
    have hD : (⨅ (v : CondPortOT.FiberDual.DualPt N)
          (_ : CondPortOT.FiberDual.InV d I ρ v ∧ v.lam = lam ∧ v.s = s),
          ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal)) ≤
        ((Lag d I ρ lam s x' y : ℝ) : EReal) :=
      iInf₂_le_of_le v' hv' (EReal.coe_le_coe_iff.2 hobj')
    refine le_trans (iInf₂_le x' hx'mem) ?_
    simp only [hG, EReal.coe_neg]
    exact EReal.neg_le_neg_iff.2 hD
