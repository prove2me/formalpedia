-- Prove2me | solution 1 for CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/26935e99-f3f9-5f45-8eb9-2fbc95246d88

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups

noncomputable section

namespace P2MKcLEVEL

variable {M : ℕ} [NeZero M]

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

theorem nsmul_V (n : ℕ) (v : V M) : n • v = ((n : ZMod M) * v.1, (n : ZMod M) * v.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem val_nsmul_V (u : ZMod M) (v : V M) : u.val • v = (u * v.1, u * v.2) := by
  rw [nsmul_V, ZMod.natCast_zmod_val]

theorem M_nsmul_V (v : V M) : M • v = 0 := by
  rw [nsmul_V, ZMod.natCast_self]; simp

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (v : V M) : Set (V M) :=
  {w | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ w = (u : ZMod M).val • v}

theorem mem_orb_self (v : V M) : v ∈ orb H v :=
  ⟨1, Subgroup.one_mem _, by rw [val_nsmul_V]; simp⟩

theorem orb_eq_of_mem {v w : V M} (hw : w ∈ orb H v) : orb H w = orb H v := by
  obtain ⟨u, hu, rfl⟩ := hw
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * u, Subgroup.mul_mem _ ht hu, ?_⟩
    rw [val_nsmul_V, val_nsmul_V, val_nsmul_V, Units.val_mul]
    ext <;> simp [mul_assoc]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * u⁻¹, Subgroup.mul_mem _ ht (Subgroup.inv_mem _ hu), ?_⟩
    rw [val_nsmul_V, val_nsmul_V, val_nsmul_V, Units.val_mul]
    ext <;> simp [mul_assoc]

abbrev ent (M : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((g i j : ℤ) : ZMod M)

abbrev row (M : ℕ) (g : SL(2, ℤ)) : V M := (ent M g 1 0, ent M g 1 1)

def ract (v : V M) (g : SL(2, ℤ)) : V M :=
  (v.1 * ent M g 0 0 + v.2 * ent M g 1 0, v.1 * ent M g 0 1 + v.2 * ent M g 1 1)

theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent M (g * h) i j = ent M g i 0 * ent M h 0 j + ent M g i 1 * ent M h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem ent_one (i j : Fin 2) : ent M 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

theorem ent_neg (g : SL(2, ℤ)) (i j : Fin 2) : ent M (-g) i j = -ent M g i j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_neg]
  rw [Matrix.neg_apply]
  push_cast
  rfl

theorem ract_one (v : V M) : ract v 1 = v := by
  simp only [ract, ent_one]
  simp

theorem ract_mul (v : V M) (g h : SL(2, ℤ)) : ract v (g * h) = ract (ract v g) h := by
  simp only [ract, ent_mul]
  ext <;> ring

theorem row_mul (g h : SL(2, ℤ)) : row M (g * h) = ract (row M g) h := by
  simp only [row, ract, ent_mul]

theorem row_neg (g : SL(2, ℤ)) : row M (-g) = -row M g := by
  simp only [row, ent_neg]; rfl

theorem ract_injective (g : SL(2, ℤ)) : Function.Injective (fun v : V M => ract v g) := by
  intro v w h
  have := congrArg (fun z => ract z g⁻¹) h
  simpa only [← ract_mul, mul_inv_cancel, ract_one] using this

theorem ract_zero_u (u : ZMod M) (a : SL(2, ℤ)) : ract ((0 : ZMod M), u) a = u.val • row M a := by
  rw [val_nsmul_V]
  simp [ract]

theorem det_row (a : SL(2, ℤ)) : ent M a 0 0 * ent M a 1 1 - ent M a 0 1 * ent M a 1 0 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe a
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  simpa [ent, mul_comm] using h

theorem addOrderOf_eq_of_combination (v : V M) (x y : ZMod M) (h : x * v.1 + y * v.2 = 1) :
    addOrderOf v = M := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (M_nsmul_V v)
  · have h0 : addOrderOf v • v = 0 := addOrderOf_nsmul_eq_zero v
    rw [nsmul_V] at h0
    have h1 : (addOrderOf v : ZMod M) * v.1 = 0 := congrArg Prod.fst h0
    have h2 : (addOrderOf v : ZMod M) * v.2 = 0 := congrArg Prod.snd h0
    have : (addOrderOf v : ZMod M) = 0 := by
      calc (addOrderOf v : ZMod M) = (addOrderOf v : ZMod M) * (x * v.1 + y * v.2) := by rw [h, mul_one]
        _ = x * ((addOrderOf v : ZMod M) * v.1) + y * ((addOrderOf v : ZMod M) * v.2) := by ring
        _ = 0 := by rw [h1, h2]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp this

theorem addOrderOf_row (a : SL(2, ℤ)) : addOrderOf (row M a) = M :=
  addOrderOf_eq_of_combination (row M a) (-ent M a 0 1) (ent M a 0 0)
    (by have := det_row (M := M) a; linear_combination this)

theorem exists_combination_of_addOrderOf_eq (v : V M) (hv : addOrderOf v = M) :
    ∃ x y : ZMod M, x * v.1 + y * v.2 = 1 := by
  set c : ℕ := v.1.val with hc
  set d : ℕ := v.2.val with hd
  have hcv : (c : ZMod M) = v.1 := ZMod.natCast_zmod_val v.1
  have hdv : (d : ZMod M) = v.2 := ZMod.natCast_zmod_val v.2
  set g : ℕ := Nat.gcd c d with hg
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

  have hcop : Nat.Coprime g M := by
    apply Nat.coprime_of_dvd
    intro k hk hkg hkM
    have hkc : k ∣ c := hkg.trans (Nat.gcd_dvd_left c d)
    have hkd : k ∣ d := hkg.trans (Nat.gcd_dvd_right c d)
    obtain ⟨m, hm⟩ := hkM
    have hcast : ∀ t : ℕ, k ∣ t → ((m * t : ℕ) : ZMod M) = 0 := by
      intro t ht
      obtain ⟨t', rfl⟩ := ht
      have : m * (k * t') = M * t' := by rw [hm]; ring
      rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hmv : m • v = 0 := by
      rw [nsmul_V, ← hcv, ← hdv, ← Nat.cast_mul, ← Nat.cast_mul, hcast c hkc, hcast d hkd]
      rfl
    have hdvd : M ∣ m := by rw [← hv]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hmv
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne M hm)
    have hle : M ≤ m := Nat.le_of_dvd hmpos hdvd
    have hlt : m < M := by
      rw [hm]
      exact lt_mul_of_one_lt_left hmpos hk.one_lt
    omega

  obtain ⟨w, hw⟩ := (ZMod.isUnit_iff_coprime g M).mpr hcop
  have hbez := Nat.gcd_eq_gcd_ab c d
  have hbez' : (g : ZMod M) = v.1 * (Nat.gcdA c d : ZMod M) + v.2 * (Nat.gcdB c d : ZMod M) := by
    have h := congrArg (fun z : ℤ => (z : ZMod M)) hbez
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul] at h
    rw [hcv, hdv] at h
    exact h
  refine ⟨(w⁻¹ : (ZMod M)ˣ) * (Nat.gcdA c d : ZMod M), (w⁻¹ : (ZMod M)ˣ) * (Nat.gcdB c d : ZMod M), ?_⟩
  calc _ = ((w⁻¹ : (ZMod M)ˣ) : ZMod M) * (v.1 * (Nat.gcdA c d : ZMod M) + v.2 * (Nat.gcdB c d : ZMod M)) := by
        ring
    _ = 1 := by rw [← hbez', ← hw, Units.inv_mul]

theorem exists_row_eq (v : V M) (hv : addOrderOf v = M) :
    ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2 := by
  obtain ⟨x, y, hxy⟩ := exists_combination_of_addOrderOf_eq v hv
  let A' : SL(2, ZMod M) := ⟨!![y, -x; v.1, v.2], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  obtain ⟨a, ha⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod M A'
  have hent : ∀ i j, ((a i j : ℤ) : ZMod M) = (A' : Matrix (Fin 2) (Fin 2) (ZMod M)) i j := by
    intro i j
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) ha
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast] at h
    exact h
  refine ⟨a, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem zpow_eq_or_of_sq {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hk : g ^ k = g ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul]
    rw [show (g ^ (2 : ℤ)) = 1 by exact_mod_cast hg, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h, zpow_zero]
  · right; rw [hk, h, zpow_one]

theorem mem_zpowers_neg_one_units {u : (ZMod M)ˣ} (hu : u ∈ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    u = 1 ∨ u = -1 := by
  obtain ⟨k, rfl⟩ := hu
  exact zpow_eq_or_of_sq (-1 : (ZMod M)ˣ) (by rw [neg_one_sq]) k

theorem mem_Hpm_iff (u : (ZMod M)ˣ) : u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    rcases mem_zpowers_neg_one_units hz with rfl | rfl
    · exact Or.inl (by rwa [mul_one])
    · exact Or.inr (by rwa [mul_neg_one, neg_neg])
  · rintro (hu | hu)
    · exact Subgroup.mem_sup_left hu
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers _)

theorem mem_zpowers_neg_one_SL {n : SL(2, ℤ)} (hn : n ∈ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    n = 1 ∨ n = -1 := by
  obtain ⟨k, rfl⟩ := hn
  exact zpow_eq_or_of_sq (-1 : SL(2, ℤ)) (by rw [neg_one_sq]) k

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases mem_zpowers_neg_one_SL hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_sup_zpowers_neg_one_iff (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ)) :
    σ ∈ Γ ⊔ Subgroup.zpowers (-1) ↔ σ ∈ Γ ∨ -σ ∈ Γ := by
  constructor
  · intro h
    have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [Subgroup.mul_normal] at h'
    obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
    rcases mem_zpowers_neg_one_SL hn with rfl | rfl
    · exact Or.inl (by simpa using hγ)
    · exact Or.inr (by simpa using hγ)
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : σ = -σ * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers _)

theorem row_of_mem_GammaH {σ : SL(2, ℤ)} (hσ : σ ∈ CohCarrier.GammaH M H) :
    ∃ u : (ZMod M)ˣ, u ∈ H ∧ row M σ = (0, (u : ZMod M)) := by
  obtain ⟨hσ0, hσH⟩ := CohCarrier.mem_GammaH_iff.mp hσ
  refine ⟨CohCarrier.gamma0Units M ⟨σ, hσ0⟩, hσH, ?_⟩
  have h10 : ent M σ 1 0 = 0 := CongruenceSubgroup.Gamma0_mem.mp hσ0
  refine Prod.ext h10 ?_
  rw [CohCarrier.val_gamma0Units]
  rfl

theorem mem_GammaH_of_row {σ : SL(2, ℤ)} {u : (ZMod M)ˣ} (hu : u ∈ H)
    (hrow : row M σ = (0, (u : ZMod M))) : σ ∈ CohCarrier.GammaH M H := by
  have h10 : ent M σ 1 0 = 0 := congrArg Prod.fst hrow
  have h11 : ent M σ 1 1 = u := congrArg Prod.snd hrow
  have hσ0 : σ ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hσ0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨σ, hσ0⟩ = u := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units]
    exact h11
  rw [this]; exact hu

theorem orb_row_eq_iff (a b : SL(2, ℤ)) :
    orb H (row M a) = orb H (row M b) ↔ b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1) := by
  set σ := b * a⁻¹ with hσ
  have hb : b = σ * a := by rw [hσ, inv_mul_cancel_right]
  have hrowb : row M b = ract (row M σ) a := by rw [hb, row_mul]
  rw [mem_sup_zpowers_neg_one_iff]
  constructor
  · intro h
    have hmem : row M b ∈ orb H (row M a) := by rw [h]; exact mem_orb_self H _
    obtain ⟨u, hu, hub⟩ := hmem
    rw [hrowb, ← ract_zero_u] at hub
    have hrowσ : row M σ = (0, (u : ZMod M)) := ract_injective a hub
    rcases (mem_Hpm_iff H u).mp hu with hu' | hu'
    · exact Or.inl (mem_GammaH_of_row H hu' hrowσ)
    · refine Or.inr (mem_GammaH_of_row H hu' ?_)
      rw [row_neg, hrowσ, Units.val_neg, Prod.neg_mk, neg_zero]
  · intro h

    obtain ⟨u, hu, hrowσ⟩ : ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ row M σ = (0, (u : ZMod M)) := by
      rcases h with h | h
      · obtain ⟨u, hu, hr⟩ := row_of_mem_GammaH H h
        exact ⟨u, Subgroup.mem_sup_left hu, hr⟩
      · obtain ⟨u, hu, hr⟩ := row_of_mem_GammaH H h
        refine ⟨-u, (mem_Hpm_iff H (-u)).mpr (Or.inr (by rwa [neg_neg])), ?_⟩
        rw [row_neg] at hr
        rw [← neg_neg (row M σ), hr, Units.val_neg, Prod.neg_mk, neg_zero]
    have hmem : row M b ∈ orb H (row M a) := ⟨u, hu, by rw [hrowb, hrowσ, ract_zero_u]⟩
    exact (orb_eq_of_mem H hmem).symm

end P2MKcLEVEL
p2m_reactivate "P2MW.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff.P2MKcLEVEL"

open P2MKcLEVEL in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ v : ZMod M × ZMod M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2) ∧
    (∀ a : SL(2, ℤ), addOrderOf ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M) = M) ∧
    (∀ a b : SL(2, ℤ),
      {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} =
        {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((b 1 0 : ℤ) : ZMod M), ((b 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) :=
  ⟨exists_row_eq, addOrderOf_row, orb_row_eq_iff H⟩

end
end S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
end P2MW
export P2MW.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff (solution)
