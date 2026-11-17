-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_comp_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:45:32.636205+00:00
-- url     : https://prove2.me/submissions/eb3b1298-ffd7-4bcc-9b6c-552b8d8e3972

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



/-! B decay calculus, part 2: composition on the right with a near-translation. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Nat

noncomputable section

/-- Derivatives of order `≥ 1` of a translation have norm at most `1`. -/
lemma bt_norm_iteratedFDeriv_add_const_le (c x : ℝ × ℝ) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => p + c) x‖ ≤ 1 := by
  have e : (fun p : ℝ × ℝ => p + c) = fun p => (id : ℝ × ℝ → ℝ × ℝ) (p + c) := rfl
  rw [e, iteratedFDeriv_comp_add_right]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hid : fderiv ℝ (id : ℝ × ℝ → ℝ × ℝ) = fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ) :=
    funext fun y => fderiv_id
  rw [← norm_iteratedFDeriv_fderiv, hid]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne hj.ne']
    simp

/-- Composition on the right with a map exponentially close to a translation. -/
theorem bt_expDecay_comp_right {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (b' : ℝ) (hf : ExpDecayCInfty f b')
    (E : ℝ × ℝ → ℝ × ℝ) (b : ℝ) (hb : 0 < b) (hE : ExpDecayCInfty E b) (c : ℝ × ℝ) :
    ExpDecayCInfty (fun p => f (p + c + E p)) b' := by
  obtain ⟨⟨s₀, hfs⟩, hl⟩ := hf
  obtain ⟨⟨r₀, hr⟩, hlE⟩ := hE
  obtain ⟨C₀, s₁, hC₀⟩ := hlE 0
  have htend : Tendsto (fun s : ℝ => |C₀| * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.exp (-(b * s))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
    simpa using h1.const_mul |C₀|
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 (htend.eventually (ge_mem_nhds one_pos))
  set S := max (max (max r₀ s₁) (max s₂ 0)) (s₀ - c.1 + 1) with hS
  have hSr : r₀ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hSs₁ : s₁ ≤ S :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hSs₂ : s₂ ≤ S :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hS0 : 0 ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hSs₀ : s₀ - c.1 + 1 ≤ S := le_max_right _ _
  set U : Set (ℝ × ℝ) := Ioi S ×ˢ univ with hU
  set V : Set (ℝ × ℝ) := Ioi s₀ ×ˢ univ with hV
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hVo : IsOpen V := isOpen_Ioi.prod isOpen_univ
  have hEU : ContDiffOn ℝ ∞ E U := hr.mono (prod_mono (Ioi_subset_Ioi hSr) subset_rfl)
  set X : ℝ × ℝ → ℝ × ℝ := fun p => p + c + E p with hX
  have hXU : ContDiffOn ℝ ∞ X U :=
    ((contDiff_id.add contDiff_const).contDiffOn).add hEU
  have hsmall : ∀ p : ℝ × ℝ, S ≤ p.1 → ‖E p‖ ≤ 1 := by
    intro p hp
    have h0 := hC₀ p.1 (hSs₁.trans hp) p.2
    rw [norm_iteratedFDeriv_zero] at h0
    exact (h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans
      (hs₂ _ (hSs₂.trans hp))
  have hX1 : ∀ p : ℝ × ℝ, S ≤ p.1 → |(X p).1 - (p.1 + c.1)| ≤ 1 := by
    intro p hp
    have : (X p).1 - (p.1 + c.1) = (E p).1 := by simp only [hX, Prod.fst_add]; ring
    rw [this]
    exact (show |(E p).1| ≤ ‖E p‖ by rw [← Real.norm_eq_abs]; exact norm_fst_le _).trans
      (hsmall p hp)
  have hmaps : MapsTo X U V := by
    intro p hp
    refine ⟨?_, trivial⟩
    have h1 := hX1 p (le_of_lt hp.1)
    have h2 : S < p.1 := hp.1
    show s₀ < (X p).1
    have := (abs_le.1 h1).1
    linarith
  refine ⟨⟨S, hfs.comp hXU hmaps⟩, fun m => ?_⟩
  choose Ci si hCi using hl
  choose Ei ti hEi using hlE
  set C' : ℝ := ∑ i ∈ Finset.range (m + 1), |Ci i| with hC'
  set D : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), |Ei i| with hD
  set T : ℝ := ∑ i ∈ Finset.range (m + 1), (|si i| + |ti i|) with hT
  have hD1 : 1 ≤ D := by
    have := Finset.sum_nonneg (s := Finset.range (m + 1)) fun i _ => abs_nonneg (Ei i)
    linarith
  have hsiT : ∀ i ≤ m, |si i| + |ti i| ≤ T := fun i hi =>
    Finset.single_le_sum (f := fun i => |si i| + |ti i|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_range.2 (by omega))
  have hCiC : ∀ i ≤ m, Ci i ≤ C' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Ci i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  have hEiD : ∀ i ≤ m, |Ei i| ≤ D - 1 := fun i hi => by
    have := Finset.single_le_sum (f := fun i => |Ei i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (show i < m + 1 by omega))
    simp only [hD]; linarith
  set K : ℝ := Real.exp (|b'|) * Real.exp (-(b' * c.1)) with hK
  refine ⟨m ! * (|C'| * K) * D ^ m, max (S + 1) (T + |c.1| + 1), fun s hs t => ?_⟩
  have hsS : S < s := by linarith [le_max_left (S + 1) (T + |c.1| + 1)]
  have hsT : T + |c.1| + 1 ≤ s := (le_max_right _ _).trans hs
  have hpU : (s, t) ∈ U := ⟨hsS, trivial⟩
  have hXs := hX1 (s, t) hsS.le
  set x1 := (X (s, t)).1 with hx1
  have hexp : Real.exp (-(b' * x1)) ≤ K * Real.exp (-(b' * s)) := by
    rw [hK, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : -(b' * x1) = -(b' * s) - b' * c.1 - b' * (x1 - (s + c.1)) := by ring
    have e2 : -(b' * (x1 - (s + c.1))) ≤ |b'| := by
      calc -(b' * (x1 - (s + c.1))) ≤ |b' * (x1 - (s + c.1))| := neg_le_abs _
        _ = |b'| * |x1 - (s + c.1)| := abs_mul _ _
        _ ≤ |b'| * 1 := mul_le_mul_of_nonneg_left hXs (abs_nonneg _)
        _ = |b'| := mul_one _
    linarith
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := m) (N := ∞) hfs hXU
    (by exact_mod_cast le_top) hVo.uniqueDiffOn hUo.uniqueDiffOn hmaps hpU
    (C := |C'| * K * Real.exp (-(b' * s))) (D := D) (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen m hUo hpU] at key
    have e : (f ∘ X) = fun p => f (p + c + E p) := rfl
    rw [e] at key
    calc _ ≤ _ := key
      _ = m ! * (|C'| * K) * D ^ m * Real.exp (-(b' * s)) := by ring
  · rw [iteratedFDerivWithin_of_isOpen i hVo (hmaps hpU)]
    have hx1s : si i ≤ x1 := by
      have := (abs_le.1 hXs).1
      have h3 := hsiT i hi
      have h4 := le_abs_self (si i)
      have h5 := neg_abs_le c.1
      have h6 := abs_nonneg (ti i)
      linarith
    have hb := hCi i x1 hx1s (X (s, t)).2
    calc ‖iteratedFDeriv ℝ i f (X (s, t))‖ = ‖iteratedFDeriv ℝ i f (x1, (X (s, t)).2)‖ := rfl
      _ ≤ Ci i * Real.exp (-(b' * x1)) := hb
      _ ≤ |C'| * Real.exp (-(b' * x1)) :=
          mul_le_mul_of_nonneg_right ((hCiC i hi).trans (le_abs_self _)) (Real.exp_pos _).le
      _ ≤ |C'| * (K * Real.exp (-(b' * s))) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = |C'| * K * Real.exp (-(b' * s)) := by ring
  · rw [iteratedFDerivWithin_of_isOpen i hUo hpU]
    have hca : ContDiffAt ℝ i (fun p : ℝ × ℝ => p + c) (s, t) :=
      (contDiff_id.add contDiff_const).contDiffAt
    have hEa : ContDiffAt ℝ i E (s, t) :=
      (hEU.contDiffAt (hUo.mem_nhds hpU)).of_le (by exact_mod_cast le_top)
    have e : X = (fun p : ℝ × ℝ => p + c) + E := rfl
    rw [e, iteratedFDeriv_add_apply hca hEa]
    have hti : ti i ≤ s := by
      have := hsiT i hi
      have h4 := le_abs_self (ti i)
      have h5 := abs_nonneg (si i)
      have h6 := abs_nonneg c.1
      linarith
    have hEb := hEi i s hti t
    have hη1 : Real.exp (-(b * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hEb' : ‖iteratedFDeriv ℝ i E (s, t)‖ ≤ D - 1 :=
      hEb.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
        ((mul_le_of_le_one_right (abs_nonneg _) hη1).trans (hEiD i hi)))
    calc _ ≤ ‖iteratedFDeriv ℝ i (fun p : ℝ × ℝ => p + c) (s, t)‖ +
          ‖iteratedFDeriv ℝ i E (s, t)‖ := norm_add_le _ _
      _ ≤ 1 + (D - 1) := add_le_add (bt_norm_iteratedFDeriv_add_const_le c _ hi1) hEb'
      _ = D := by ring
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff Real

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (b' : ℝ) (hf : ExpDecayCInfty f b')
    (E : ℝ × ℝ → ℝ × ℝ) (b : ℝ) (hb : 0 < b) (hE : ExpDecayCInfty E b) (c : ℝ × ℝ) :
    ExpDecayCInfty (fun p => f (p + c + E p)) b' :=
  bt_expDecay_comp_right f b' hf E b hb hE c
