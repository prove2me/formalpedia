-- Prove2me | solution 1 for DavisGallegoTopaloglu2014.theorem_12_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:05:10.66455+00:00
-- url     : https://prove2.me/submissions/aacb0130-8d20-4357-ac0c-22f35e303b88

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Model
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

open NestedLogitVariants.PowersDelta

theorem dg86_x_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.PowersDelta.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j)
    (A : ι → Set (Finset (Fin n))) (hA : ∀ i, ∅ ∈ A i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hV : ∀ i S, 0 ≤ V I i S := fun i S =>
    add_nonneg (hvnp i) (Finset.sum_nonneg fun j _ => hv i j)
  have hnw : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hV i S) _
  have hR : ∀ i S, 0 ≤ R I i S := fun i S =>
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)) (hV i S)
  obtain ⟨⟨hf1, hf2⟩, hmin⟩ := hopt
  by_contra hx
  push Not at hx
  have hy0 : ∀ i, 0 ≤ yh i := fun i =>
    le_trans (mul_nonneg (hnw i ∅) (by linarith [hR i ∅])) (hf2 i ∅ (hA i))
  have hsum0 : 0 ≤ ∑ i, yh i := Finset.sum_nonneg fun i _ => hy0 i
  have hv0x : I.v0 * xh ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hx.le
  have hsum : ∑ i, yh i = 0 := by linarith
  have hyz : ∀ i, yh i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hsum i (Finset.mem_univ i)
  have hv0z : I.v0 = 0 := by
    by_contra h
    have : 0 < I.v0 := lt_of_le_of_ne hv0 (Ne.symm h)
    nlinarith
  have hnw0 : ∀ i, ∀ S ∈ A i, nestWeight I i S = 0 := by
    intro i S hS
    have h := hf2 i S hS
    rw [hyz i] at h
    have h1 := hnw i S
    have h2 := hR i S
    by_contra hne
    have : 0 < nestWeight I i S := lt_of_le_of_ne h1 (Ne.symm hne)
    nlinarith
  have hfeas : LP4Feasible I A (xh - 1) yh := by
    refine ⟨by rw [hsum, hv0z]; simp, ?_⟩
    intro i S hS
    rw [hnw0 i S hS, hyz i]; simp
  have := hmin _ _ hfeas
  linarith

theorem dg86_core (a b δ γ γbar xh NS NT : ℝ) (hapos : 0 < a) (hbpos : 0 < b)
    (hab : a ≤ δ * b) (hba : b ≤ δ * a) (hγ0 : 0 ≤ γ) (hγi : γ ≤ γbar) (hγbar1 : 1 < γbar)
    (hδ : 1 < δ) (hx : 0 ≤ xh) (hNSn : 0 ≤ NS) (hNS : NS ≤ δ * NT) :
    NS * a ^ (γ - 1) - δ ^ (2 * γbar + 1) * xh * a ^ γ ≤
      δ ^ (γbar + 1) * (NT * b ^ (γ - 1) - xh * b ^ γ) := by
  have hδ0 : 0 < δ := by linarith
  have hD1pos : 0 < δ ^ (γbar + 1) := Real.rpow_pos_of_pos hδ0 _
  have hD1e : δ ^ (γbar + 1) = δ ^ γbar * δ := Real.rpow_add_one hδ0.ne' γbar
  have hD2e : δ ^ (2 * γbar + 1) = δ ^ γbar * δ ^ (γbar + 1) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hA1 : a ^ (γ - 1) ≤ δ ^ γbar * b ^ (γ - 1) := by
    rcases le_or_gt 1 γ with h1 | h1
    · calc a ^ (γ - 1) ≤ (δ * b) ^ (γ - 1) :=
            Real.rpow_le_rpow hapos.le hab (by linarith)
        _ = δ ^ (γ - 1) * b ^ (γ - 1) := Real.mul_rpow hδ0.le hbpos.le
        _ ≤ δ ^ γbar * b ^ (γ - 1) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbpos.le _)
            exact Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
    · have h2 : (δ * a) ^ (γ - 1) ≤ b ^ (γ - 1) :=
        Real.rpow_le_rpow_of_nonpos hbpos hba (by linarith)
      rw [Real.mul_rpow hδ0.le hapos.le] at h2
      have h3 : δ ^ (1 - γ) * δ ^ (γ - 1) = 1 := by
        rw [← Real.rpow_add hδ0]; simp
      have h4 : δ ^ (1 - γ) ≤ δ ^ γbar :=
        Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
      have h5 : 0 ≤ δ ^ (1 - γ) := Real.rpow_nonneg hδ0.le _
      have h6 : 0 ≤ b ^ (γ - 1) := Real.rpow_nonneg hbpos.le _
      calc a ^ (γ - 1) = δ ^ (1 - γ) * (δ ^ (γ - 1) * a ^ (γ - 1)) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ δ ^ (1 - γ) * b ^ (γ - 1) := mul_le_mul_of_nonneg_left h2 h5
        _ ≤ δ ^ γbar * b ^ (γ - 1) := mul_le_mul_of_nonneg_right h4 h6
  have hB : b ^ γ ≤ δ ^ γbar * a ^ γ := by
    calc b ^ γ ≤ (δ * a) ^ γ := Real.rpow_le_rpow hbpos.le hba hγ0
      _ = δ ^ γ * a ^ γ := Real.mul_rpow hδ0.le hapos.le
      _ ≤ δ ^ γbar * a ^ γ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hapos.le _)
          exact Real.rpow_le_rpow_of_exponent_le hδ.le hγi
  have hb0 : 0 ≤ b ^ (γ - 1) := Real.rpow_nonneg hbpos.le _
  have hDg : 0 ≤ δ ^ γbar := Real.rpow_nonneg hδ0.le _
  have hk1 : NS * a ^ (γ - 1) ≤ δ ^ (γbar + 1) * (NT * b ^ (γ - 1)) := by
    calc NS * a ^ (γ - 1)
        ≤ NS * (δ ^ γbar * b ^ (γ - 1)) := mul_le_mul_of_nonneg_left hA1 hNSn
      _ ≤ (δ * NT) * (δ ^ γbar * b ^ (γ - 1)) :=
          mul_le_mul_of_nonneg_right hNS (mul_nonneg hDg hb0)
      _ = δ ^ (γbar + 1) * (NT * b ^ (γ - 1)) := by rw [hD1e]; ring
  have hk2 : δ ^ (γbar + 1) * (xh * b ^ γ) ≤ δ ^ (2 * γbar + 1) * xh * a ^ γ := by
    rw [hD2e]
    have := mul_le_mul_of_nonneg_left hB (mul_nonneg hD1pos.le hx)
    linarith
  linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : NestedLogitVariants.PowersDelta.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i)) (hvL : ∀ i, 0 < vL I i)
    (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    LP3Feasible I (δ ^ (2 * γbar + 1) * xh) (δ ^ (γbar + 1) • yh) := by
  have hA : ∀ i, (∅ : Finset (Fin n)) ∈ powersCandidates I δ Sh i := fun i => Or.inr rfl
  have hx := dg86_x_nonneg I hv0 hvnp hv hr _ hA xh yh hopt
  obtain ⟨⟨hf1, hf2⟩, _⟩ := hopt
  have hV : ∀ i S, 0 ≤ V I i S := fun i S =>
    add_nonneg (hvnp i) (Finset.sum_nonneg fun j _ => hv i j)
  have hnw : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hV i S) _
  have hN : ∀ i (S : Finset (Fin n)), 0 ≤ ∑ j ∈ S, I.r i j * I.v i j := fun i S =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)
  have hδ0 : 0 < δ := by linarith
  have hD1pos : 0 < δ ^ (γbar + 1) := Real.rpow_pos_of_pos hδ0 _
  have hDg : 1 ≤ δ ^ γbar := Real.one_le_rpow hδ.le (by linarith)
  have hD1e : δ ^ (γbar + 1) = δ ^ γbar * δ := Real.rpow_add_one hδ0.ne' γbar
  have hD2e : δ ^ (2 * γbar + 1) = δ ^ γbar * δ ^ (γbar + 1) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hD12 : δ ^ (γbar + 1) ≤ δ ^ (2 * γbar + 1) := by rw [hD2e]; nlinarith
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have : 0 ≤ δ ^ (2 * γbar + 1) * xh * I.v0 := by positivity
    calc δ ^ (γbar + 1) * ∑ i, yh i ≤ δ ^ (γbar + 1) * (I.v0 * xh) := mul_le_mul_of_nonneg_left hf1 hD1pos.le
      _ = I.v0 * (δ ^ (γbar + 1) * xh) := by ring
      _ ≤ I.v0 * (δ ^ (2 * γbar + 1) * xh) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hD12 hx) hv0
  intro i S
  simp only [Pi.smul_apply, smul_eq_mul]
  have hγi : I.γ i ≤ γbar := hγbar.2 ⟨i, rfl⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    have h := hf2 i ∅ (hA i)
    have hR0 : R I i ∅ = 0 := by simp [R]
    rw [hR0] at h ⊢
    have hw := hnw i ∅
    have : nestWeight I i ∅ * xh * δ ^ (γbar + 1) ≤ nestWeight I i ∅ * xh * δ ^ (2 * γbar + 1) :=
      mul_le_mul_of_nonneg_left hD12 (mul_nonneg hw hx)
    nlinarith
  -- nonempty S
  set a := V I i S with ha
  have haL : vL I i ≤ a := by
    obtain ⟨j0, hj0⟩ := hS
    simp only [ha, V, vL]
    have h1 : Finset.univ.inf' Finset.univ_nonempty (I.v i) ≤ I.v i j0 :=
      Finset.inf'_le _ (Finset.mem_univ _)
    have h2 : I.v i j0 ≤ ∑ j ∈ S, I.v i j :=
      Finset.single_le_sum (f := fun j => I.v i j) (fun j _ => hv i j) hj0
    linarith
  have hapos : 0 < a := lt_of_lt_of_le (hvL i) haL
  have haU : a ≤ vU I i := by
    simp only [ha, vU, V]
    have : ∑ j ∈ S, I.v i j ≤ ∑ j, I.v i j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv i j)
    linarith
  set l : ℤ := ⌈Real.logb δ a⌉ with hl
  have hl1 : Real.logb δ a ≤ l := Int.le_ceil _
  have hl2 : (l : ℝ) - 1 < Real.logb δ a := by
    have := Int.ceil_lt_add_one (Real.logb δ a); rw [← hl] at this; linarith
  have hup : a ≤ δ ^ l := by
    rw [← Real.rpow_intCast]
    exact (Real.logb_le_iff_le_rpow hδ hapos).1 hl1
  have hlo : δ ^ (l - 1) ≤ a := by
    rw [← Real.rpow_intCast]
    have := (Real.lt_logb_iff_rpow_lt hδ hapos).1 (by push_cast; exact hl2)
    push_cast; exact this.le
  have hlL : lL I i δ ≤ l := by
    unfold lL; exact Int.ceil_mono (Real.logb_le_logb_of_le hδ (hvL i) haL)
  have hlU : l ≤ lU I i δ := by
    unfold lU; exact Int.ceil_mono (Real.logb_le_logb_of_le hδ hapos haU)
  have hlev : InLevel I i δ l S := ⟨hlo, hup⟩
  obtain ⟨⟨hb1, hb2⟩, hbN⟩ := hSh i l hlL hlU ⟨S, hlev⟩
  have hNS := hbN S hlev
  set T := Sh i l with hT
  set b := V I i T with hb
  have hpowpos : 0 < δ ^ (l - 1) := zpow_pos hδ0 _
  have hbpos : 0 < b := lt_of_lt_of_le hpowpos hb1
  have hzl : δ ^ l = δ ^ (l - 1) * δ := by
    rw [← zpow_add_one₀ hδ0.ne']; ring_nf
  have hab : a ≤ δ * b := by rw [hzl] at hup; nlinarith
  have hba : b ≤ δ * a := by rw [hzl] at hb2; nlinarith
  have hy := hf2 i T (Or.inl ⟨l, hlL, hlU, rfl⟩)
  -- rewrite both sides
  have eS : nestWeight I i S * (R I i S - δ ^ (2 * γbar + 1) * xh) =
      (∑ j ∈ S, I.r i j * I.v i j) * a ^ (I.γ i - 1) - δ ^ (2 * γbar + 1) * xh * a ^ I.γ i := by
    simp only [nestWeight, R, ← ha]
    rw [Real.rpow_sub_one hapos.ne']; field_simp
  have eT : nestWeight I i T * (R I i T - xh) =
      (∑ j ∈ T, I.r i j * I.v i j) * b ^ (I.γ i - 1) - xh * b ^ I.γ i := by
    simp only [nestWeight, R, ← hb]
    rw [Real.rpow_sub_one hbpos.ne']; field_simp
  rw [eT] at hy
  rw [eS]
  have := dg86_core a b δ (I.γ i) γbar xh _ _ hapos hbpos hab hba (hγ0 i) hγi hγbar1 hδ hx
    (hN i S) hNS
  nlinarith [mul_le_mul_of_nonneg_left hy hD1pos.le]
