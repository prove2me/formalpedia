-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/74a2fb98-69d4-5697-972d-d0f35242e51b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
import Theorems.Thm_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace RigidUniq

p2m_open "CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]

theorem act_pow_comp_act_pow (Y : FormalODModule p B) (a b : ℕ) :
    (Y.act ((p : Zp2 p) ^ a)).comp (Y.act ((p : Zp2 p) ^ b)) = Y.act ((p : Zp2 p) ^ (a + b)) := by
  rw [← Y.act_mul, ← pow_add]

theorem act_pow_zero (Y : FormalODModule p B) (a : ℕ) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Y.act ((p : Zp2 p) ^ a) i) = 0 := (Y.isLawHom_act _).1 i

theorem hom_eq_of_comp_act_pow_eq [IsNoetherianRing B] (X X' : FormalODModule p B) (hX4 : X.HasHeight 4) :
    ∀ (k : ℕ) (χ χ' : FormalODModule.Hom X X'),
      χ.toSeries.comp (X.act ((p : Zp2 p) ^ k)) = χ'.toSeries.comp (X.act ((p : Zp2 p) ^ k)) → χ = χ' := by
  have hq0 : ∀ i, MvPowerSeries.constantCoeff (X.act ((p : ℕ) : Zp2 p) i) = 0 := (X.isLawHom_act _).1
  have hk1 : FormalODModule.HasKernelOfDegree (X.act (((p : ℕ) : Zp2 p) ^ 1)) (p ^ 4) := by
    rw [pow_one]; exact hX4
  have cancel : ∀ χ χ' : FormalODModule.Hom X X',
      χ.toSeries.comp (X.act ((p : ℕ) : Zp2 p)) = χ'.toSeries.comp (X.act ((p : ℕ) : Zp2 p)) → χ = χ' := by
    intro χ χ' hχ
    refine CerednikDrinfeld.FormalODModule.Hom.eq_of_comp_act_pow_eq_of_hasKernelOfDegree 1 (p ^ 4) hk1 χ χ' ?_
    rw [pow_one]; exact hχ
  intro k
  induction k with
  | zero =>
    intro χ χ' h
    apply FormalODModule.Hom.ext
    have h1 : X.act (((p : ℕ) : Zp2 p) ^ 0) = Series.id B := by rw [pow_zero, X.act_one]
    rwa [h1, Series.comp_id, Series.comp_id] at h
  | succ k ih =>
    intro χ χ' h
    have hk : (χ.comp ⟨X.act (((p : ℕ) : Zp2 p) ^ k), FormalODModule.IsODHom.act_natCast_pow X k⟩) =
        (χ'.comp ⟨X.act (((p : ℕ) : Zp2 p) ^ k), FormalODModule.IsODHom.act_natCast_pow X k⟩) := by
      apply cancel
      show (χ.toSeries.comp (X.act (((p : ℕ) : Zp2 p) ^ k))).comp (X.act ((p : ℕ) : Zp2 p)) =
        (χ'.toSeries.comp (X.act (((p : ℕ) : Zp2 p) ^ k))).comp (X.act ((p : ℕ) : Zp2 p))
      rw [Series.comp_assoc _ _ _ (X.isLawHom_act _).1 hq0, Series.comp_assoc _ _ _ (X.isLawHom_act _).1 hq0,
        ← X.act_mul, ← pow_succ]
      exact h
    exact ih χ χ' (congrArg FormalODModule.Hom.toSeries hk)

end RigidUniq

open RigidUniq in
theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (ι : Zp2 p →+* O) (ψ : O →+* B) (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (u₁ u₂ : Series B) (m₁ m₂ : ℕ)
    (hu₁ : FormalODModule.IsODHom t.X t'.X u₁) (hu₂ : FormalODModule.IsODHom t.X t'.X u₂)
    (h₁ : (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t'.n))).comp
        ((u₁.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t.n))).comp t'.ρ)
    (h₂ : (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t'.n))).comp
        ((u₂.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t.n))).comp t'.ρ) :
    u₁ = u₂ := by

  set mk := Ideal.Quotient.mk (pIdeal p B) with hmk
  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := ht.constantCoeff_ρ
  have hρker : FormalODModule.HasKernelOfDegree t.ρ (p ^ (4 * t.n)) := ht.2.2.2
  have hX4 : t.X.HasHeight 4 := ht.2.1
  have hA0 : ∀ (a : ℕ) i, MvPowerSeries.constantCoeff (t'.Xbar.act ((p : Zp2 p) ^ a) i) = 0 :=
    fun a => act_pow_zero t'.Xbar a
  have hAX0 : ∀ (a : ℕ) i, MvPowerSeries.constantCoeff (t.Xbar.act ((p : Zp2 p) ^ a) i) = 0 :=
    fun a => act_pow_zero t.Xbar a
  have hū : ∀ (u : Series B), FormalODModule.IsODHom t.X t'.X u →
      FormalODModule.IsODHom t.Xbar t'.Xbar (u.map mk) := fun u hu => hu.map mk
  have hūρ : ∀ (u : Series B), FormalODModule.IsODHom t.X t'.X u →
      ∀ i, MvPowerSeries.constantCoeff (((u.map mk).comp t.ρ) i) = 0 :=
    fun u hu => Series.constantCoeff_comp (hu.map mk).constantCoeff hρ0

  have step1 : ∀ (u : Series B) (m m' : ℕ), FormalODModule.IsODHom t.X t'.X u →
      (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map mk).comp t.ρ) =
        (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ →
      (t'.Xbar.act ((p : Zp2 p) ^ (m' + m + t'.n))).comp ((u.map mk).comp t.ρ) =
        (t'.Xbar.act ((p : Zp2 p) ^ (m' + m + t.n))).comp t'.ρ := by
    intro u m m' hu h
    have := congrArg (fun s => (t'.Xbar.act ((p : Zp2 p) ^ m')).comp s) h
    rw [← Series.comp_assoc _ _ _ (hA0 _) (hūρ u hu), act_pow_comp_act_pow, ← add_assoc,
      ← Series.comp_assoc _ _ _ (hA0 _) hρ', act_pow_comp_act_pow, ← add_assoc] at this
    exact this
  set N := m₁ + m₂ + t'.n with hN
  have e1 : (t'.Xbar.act ((p : Zp2 p) ^ N)).comp ((u₁.map mk).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + m₁ + t.n))).comp t'.ρ := by
    have := step1 u₁ m₁ m₂ hu₁ h₁
    rw [hN, show m₁ + m₂ = m₂ + m₁ from Nat.add_comm _ _]
    exact this
  have e2 : (t'.Xbar.act ((p : Zp2 p) ^ N)).comp ((u₂.map mk).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + m₁ + t.n))).comp t'.ρ := by
    have := step1 u₂ m₂ m₁ hu₂ h₂
    rw [show m₂ + m₁ = m₁ + m₂ from Nat.add_comm _ _]
    exact this
  have e12 : (t'.Xbar.act ((p : Zp2 p) ^ N)).comp ((u₁.map mk).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ N)).comp ((u₂.map mk).comp t.ρ) := by rw [e1, e2]

  have step2 : ∀ (u : Series B), FormalODModule.IsODHom t.X t'.X u →
      (t'.Xbar.act ((p : Zp2 p) ^ N)).comp ((u.map mk).comp t.ρ) =
        (((u.comp (t.X.act ((p : Zp2 p) ^ N))).map mk).comp t.ρ) := by
    intro u hu
    rw [← Series.comp_assoc _ _ _ (hū u hu).constantCoeff hρ0, ← (hū u hu).2.1,
      Series.map_comp mk _ _ (act_pow_zero t.X N)]
    rfl
  rw [step2 u₁ hu₁, step2 u₂ hu₂] at e12

  have e3 : (u₁.comp (t.X.act ((p : Zp2 p) ^ N))).map mk = (u₂.comp (t.X.act ((p : Zp2 p) ^ N))).map mk := by
    funext i
    exact CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree t.ρ hρ0 hρker _ _
      (congrFun e12 i)

  obtain ⟨ν, hν⟩ := hB
  have hker : RingHom.ker mk ^ (ν + 1) = ⊥ := by
    rw [hmk, Ideal.mk_ker, eq_bot_iff]
    refine le_trans (Ideal.pow_le_pow_right (Nat.le_succ ν)) ?_
    rw [pIdeal, Ideal.span_singleton_pow, hν, Ideal.span_singleton_eq_bot.mpr rfl]
  have hw₁ : FormalODModule.IsODHom t.X t'.X (u₁.comp (t.X.act ((p : Zp2 p) ^ N))) :=
    hu₁.comp (FormalODModule.IsODHom.act_natCast_pow t.X N)
  have hw₂ : FormalODModule.IsODHom t.X t'.X (u₂.comp (t.X.act ((p : Zp2 p) ^ N))) :=
    hu₂.comp (FormalODModule.IsODHom.act_natCast_pow t.X N)
  have e4 := (CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
    p mk ν hker ν hν t.X t'.X).1 _ _ hw₁ hw₂ e3

  have step5 : ∀ (u : Series B), FormalODModule.IsODHom t.X t'.X u →
      (t'.X.act ((p : Zp2 p) ^ (ν * ν))).comp (u.comp (t.X.act ((p : Zp2 p) ^ N))) =
        u.comp (t.X.act ((p : Zp2 p) ^ (ν * ν + N))) := by
    intro u hu
    rw [← Series.comp_assoc _ _ _ hu.constantCoeff (act_pow_zero t.X N), ← hu.2.1,
      Series.comp_assoc _ _ _ (act_pow_zero t.X _) (act_pow_zero t.X N), act_pow_comp_act_pow]
  rw [step5 u₁ hu₁, step5 u₂ hu₂] at e4

  have := hom_eq_of_comp_act_pow_eq t.X t'.X hX4 (ν * ν + N) ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ e4
  exact congrArg FormalODModule.Hom.toSeries this

end S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq (solution)
