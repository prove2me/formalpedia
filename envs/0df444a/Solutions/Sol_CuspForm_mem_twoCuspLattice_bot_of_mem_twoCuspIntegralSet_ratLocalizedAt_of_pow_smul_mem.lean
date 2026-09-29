-- Prove2me | solution 1 for CuspForm.mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/58f6007e-9b64-5e4c-865a-3503544ab987

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem

set_option autoImplicit false

open scoped TensorProduct MatrixGroups ModularForm

namespace SatCmp

open ModularFormClass CohCarrier

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (p : ℕ)

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_coe_add (f g : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g, map_add]

theorem qCoeff_coe_neg (f : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(-f)) n = -qCoeff (⇑f) n := by
  unfold qCoeff
  rw [CuspForm.coe_neg, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qCoeff_zero (n : ℕ) : qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_coe_nsmul (m : ℕ) (f : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(m • f)) n = (m : ℂ) * qCoeff (⇑f) n := by
  induction m with
  | zero => rw [zero_smul, CuspForm.coe_zero, qCoeff_zero, Nat.cast_zero, zero_mul]
  | succ m ih => rw [add_smul, one_smul, qCoeff_coe_add, ih, Nat.cast_succ]; ring

theorem qCoeff_coe_zsmul (m : ℤ) (f : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(m • f)) n = (m : ℂ) * qCoeff (⇑f) n := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · rw [natCast_zsmul, qCoeff_coe_nsmul, Int.cast_natCast]
  · rw [neg_smul, natCast_zsmul, qCoeff_coe_neg, qCoeff_coe_nsmul, Int.cast_neg, Int.cast_natCast]; ring

section WSlash

variable (hW : ∀ (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (GammaH M H) 2),
  ∃ X : CuspForm (GammaH M H) 2, ⇑X = ModularForm.alSlash W 2 ⇑f)
include hW

theorem add_mem_set {f g : CuspForm (GammaH M H) 2}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    f + g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
  intro t ht W n
  obtain ⟨Xf, hXf⟩ := hW W (t f)
  obtain ⟨Xg, hXg⟩ := hW W (t g)
  rw [map_add]
  refine ⟨?_, ?_⟩
  · rw [qCoeff_coe_add]; exact Subring.add_mem _ (hf t ht W n).1 (hg t ht W n).1
  · rw [CuspForm.coe_add, ModularForm.alSlash_add, ← hXf, ← hXg, ← CuspForm.coe_add, qCoeff_coe_add, hXf, hXg]
    exact Subring.add_mem _ (hf t ht W n).2 (hg t ht W n).2

theorem neg_mem_set {f : CuspForm (GammaH M H) 2}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    -f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
  intro t ht W n
  obtain ⟨Xf, hXf⟩ := hW W (t f)
  rw [map_neg]
  refine ⟨?_, ?_⟩
  · rw [qCoeff_coe_neg]; exact Subring.neg_mem _ (hf t ht W n).1
  · have : ModularForm.alSlash W 2 ⇑(-(t f)) = ⇑(-Xf) := by
      rw [CuspForm.coe_neg, CuspForm.coe_neg, hXf, ModularForm.alSlash_def, ModularForm.alSlash_def, SlashAction.neg_slash]
    rw [this, qCoeff_coe_neg, hXf]
    exact Subring.neg_mem _ (hf t ht W n).2

theorem mem_set_of_mem_lattice {g : CuspForm (GammaH M H) 2}
    (hg : g ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact CuspForm.zero_mem_twoCuspIntegralSet M H 2 p ⊥
  | add x y _ _ hx hy => exact add_mem_set p hW hx hy
  | smul a x _ hx =>
    obtain ⟨m, hm⟩ := Subring.mem_bot.mp a.2
    have : a • x = m • x := by
      rw [Subring.smul_def, show (a : ℂ) = (m : ℂ) from hm.symm, Int.cast_smul_eq_zsmul]
    rw [this]
    clear this hm
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · rw [natCast_zsmul]
      induction k with
      | zero => rw [zero_smul]; exact CuspForm.zero_mem_twoCuspIntegralSet M H 2 p ⊥
      | succ k ih => rw [add_smul, one_smul]; exact add_mem_set p hW ih hx
    · rw [neg_smul, natCast_zsmul]
      refine neg_mem_set p hW ?_
      induction k with
      | zero => rw [zero_smul]; exact CuspForm.zero_mem_twoCuspIntegralSet M H 2 p ⊥
      | succ k ih => rw [add_smul, one_smul]; exact add_mem_set p hW ih hx

end WSlash

theorem mem_bot_of_pow_mul_mem_bot [hp : Fact p.Prime] (c : ℂ)
    (hc : c ∈ (GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) (a : ℕ)
    (hpc : (p : ℂ) ^ a * c ∈ (⊥ : Subring ℂ)) : c ∈ (⊥ : Subring ℂ) := by
  obtain ⟨r, hr, rfl⟩ := Subring.mem_map.mp hc
  obtain ⟨m, hm⟩ := Subring.mem_bot.mp hpc

  have hq : (p : ℚ) ^ a * r = (m : ℚ) := by
    apply (algebraMap ℚ ℂ).injective
    rw [map_mul, map_pow, map_natCast, map_intCast]
    exact hm.symm
  have hp0 : ((p : ℚ)) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hr' : r = Rat.divInt m ((p : ℤ) ^ a) := by
    rw [Rat.divInt_eq_div, eq_div_iff (by exact_mod_cast hp0)]
    push_cast
    rw [mul_comm]; exact hq

  have hdenZ : (r.den : ℤ) ∣ (p : ℤ) ^ a := by rw [hr']; exact Rat.den_dvd m _
  have hden : r.den ∣ p ^ a := by exact_mod_cast hdenZ
  have hcop : r.den.Coprime p := hr
  have hden1 : r.den = 1 := Nat.Coprime.eq_one_of_dvd (hcop.pow_right a) hden
  refine Subring.mem_bot.mpr ⟨r.num, ?_⟩
  rw [← map_intCast (algebraMap ℚ ℂ), Rat.coe_int_num_of_den_eq_one hden1]

end SatCmp

open SatCmp ModularFormClass CohCarrier in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (z : CuspForm (CohCarrier.GammaH M H) 2)
    (hz : z ∈ CuspForm.twoCuspIntegralSet M H 2 p ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)))
    (a : ℕ) (ha : ((p : ℂ) ^ a) • z ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    z ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) := by
  have hp : p.Prime := Fact.out

  have hW : ∀ (W : ModularForm.AtkinLehnerDatum M p) (g : CuspForm (GammaH M H) 2),
      ∃ X : CuspForm (GammaH M H) 2, ⇑X = ModularForm.alSlash W 2 ⇑g := by
    intro W g
    have hR : W.R = M / p := by
      calc W.R = p * W.R / p := (Nat.mul_div_cancel_left _ hp.pos).symm
        _ = M / p := by rw [← W.hM]
    have hHp' : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
      intro u hu
      apply hHp u
      have key : ∀ (d : ℕ) (hd : d ∣ M), d = M / p → ZMod.unitsMap hd u = 1 →
          ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 := by
        intro d hd hdd h; subst hdd; exact h
      exact key W.R _ hR hu
    exact CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp' 2 g

  have hsat := mem_set_of_mem_lattice p hW ha

  refine CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (fun t ht W n => ?_)
  obtain ⟨hz1, hz2⟩ := hz t ht W n
  obtain ⟨hs1, hs2⟩ := hsat t ht W n

  have hlin : t (((p : ℂ) ^ a) • z) = (p ^ a : ℕ) • t z := by
    rw [LinearMap.map_smul, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow]
  rw [hlin] at hs1 hs2
  refine ⟨mem_bot_of_pow_mul_mem_bot p _ hz1 a ?_, mem_bot_of_pow_mul_mem_bot p _ hz2 a ?_⟩
  · rw [qCoeff_coe_nsmul, Nat.cast_pow] at hs1
    exact hs1
  · obtain ⟨X, hX⟩ := hW W (t z)
    have h2 : ∀ m : ℕ, ModularForm.alSlash W 2 ⇑(m • t z) = ⇑(m • X) := by
      intro m
      induction m with
      | zero =>
        rw [zero_smul, zero_smul, CuspForm.coe_zero, ModularForm.alSlash_def]
        exact SlashAction.zero_slash 2 _
      | succ m ih =>
        rw [add_smul, one_smul, add_smul, one_smul, CuspForm.coe_add, ModularForm.alSlash_add, ih, ← hX,
          ← CuspForm.coe_add]
    rw [h2, qCoeff_coe_nsmul, Nat.cast_pow, hX] at hs2
    exact hs2

end S_CuspForm_mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem
end P2MW
export P2MW.S_CuspForm_mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem (solution)
