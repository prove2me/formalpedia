-- Prove2me | solution 1 for Formalism.G.log_determines_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:01:43.206505+00:00
-- url     : https://prove2.me/submissions/419216b1-c736-4cb1-8b3f-2fd8dd1d6d81

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace Formalism.G
private theorem hom_ps_subst_mv_subst {R : Type*} [CommRing R] {σ τ : Type*}
    (g : PowerSeries R) (G : MvPowerSeries σ R) (v : σ → MvPowerSeries τ R)
    (hG : MvPowerSeries.constantCoeff G = 0) (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (g.subst G) = g.subst (MvPowerSeries.subst v G) := by
  have hG' : MvPowerSeries.HasSubst (fun _ : Unit => G) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hG
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hG' hv]
private theorem hom_hasSubst_pair {R : Type*} [CommRing R] {τ : Type*}
    (a b : MvPowerSeries τ R) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.HasSubst ![a, b] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp [ha, hb]
private theorem hom_substInj {R : Type*} [CommRing R] {ι : Type*} (f : PowerSeries R)
    (a b : MvPowerSeries ι R) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    (h : f.subst a = f.subst b) : a = b := by
  classical

  let H : MvPowerSeries (Fin 2) R := fun m => coeff (m 0 + m 1 + 1) f
  have cH : ∀ m, MvPowerSeries.coeff m H = coeff (m 0 + m 1 + 1) f := fun m => rfl
  have cX : ∀ (s : Fin 2) (m : Fin 2 →₀ ℕ),
      MvPowerSeries.coeff m (f.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R)) =
        if m = Finsupp.single s (m s) then coeff (m s) f else 0 := by
    intro s m
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X s)]
    simp_rw [MvPowerSeries.coeff_X_pow]
    rw [finsum_eq_single _ (m s)]
    · split_ifs <;> simp
    · intro d hd
      rw [if_neg]
      · simp
      · intro hm
        apply hd
        rw [hm]
        simp
  have key : (MvPowerSeries.X 0 - MvPowerSeries.X 1) * H =
      f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) - f.subst (MvPowerSeries.X 1) := by
    ext m
    have e0 : m = Finsupp.single 0 (m 0) ↔ m 1 = 0 := by
      constructor
      · intro hm
        rw [hm]
        simp
      · intro hm
        ext k
        fin_cases k <;> simp [hm]
    have e1 : m = Finsupp.single 1 (m 1) ↔ m 0 = 0 := by
      constructor
      · intro hm
        rw [hm]
        simp
      · intro hm
        ext k
        fin_cases k <;> simp [hm]
    have s00 : (m - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 = m 0 - 1 := by simp
    have s01 : (m - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 = m 1 := by simp
    have s10 : (m - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = m 0 := by simp
    have s11 : (m - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 = m 1 - 1 := by simp
    rw [sub_mul, map_sub, map_sub, cX, cX, MvPowerSeries.X, MvPowerSeries.X,
      MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, cH, cH, s00, s01, s10, s11]
    simp only [Finsupp.single_le_iff, one_mul, e0, e1]
    generalize m 0 = i
    generalize m 1 = j
    rcases i with _ | i <;> rcases j with _ | j <;> simp <;> ring_nf
  have hv : MvPowerSeries.HasSubst ![a, b] := hom_hasSubst_pair a b ha hb
  have hsx : ∀ s : Fin 2, MvPowerSeries.subst ![a, b]
      (f.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R)) = f.subst (![a, b] s) := by
    intro s
    rw [hom_ps_subst_mv_subst f (MvPowerSeries.X s) ![a, b] (MvPowerSeries.constantCoeff_X s) hv,
      MvPowerSeries.subst_X hv]

  have key2 := congrArg (MvPowerSeries.substAlgHom hv) key
  simp only [map_mul, map_sub, MvPowerSeries.coe_substAlgHom] at key2
  rw [hsx 0, hsx 1, MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv] at key2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key2
  rw [h, sub_self] at key2
  have c1 : MvPowerSeries.constantCoeff (H - 1) = 0 := by
    rw [map_sub, map_one, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cH]
    simp [h1]
  have hU : IsUnit (MvPowerSeries.subst ![a, b] H) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have hsplit : H = 1 + (H - 1) := by ring
    rw [hsplit, ← MvPowerSeries.coe_substAlgHom hv, map_add, map_one, MvPowerSeries.coe_substAlgHom,
      map_add, map_one,
      MvPowerSeries.constantCoeff_subst_eq_zero hv (fun i => by fin_cases i <;> simp [ha, hb]) c1,
      add_zero]
    exact isUnit_one
  exact sub_eq_zero.1 (hU.mul_left_eq_zero.1 key2)
end Formalism.G
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.G
namespace Formalism.G
theorem _root_.solution : LogDeterminesLaw := by
  unfold LogDeterminesLaw
  intro R _ F G f hF hG
  apply FormalGroup.ext
  apply hom_substInj f _ _ hF.1 hF.2.1 F.zero_constantCoeff G.zero_constantCoeff
  rw [hF.2.2, hG.2.2]
end Formalism.G
