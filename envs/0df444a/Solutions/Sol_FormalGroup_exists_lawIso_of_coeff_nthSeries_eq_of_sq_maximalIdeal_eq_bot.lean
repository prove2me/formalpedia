-- Prove2me | solution 1 for FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4333b671-84fc-5442-8a0c-563f5cb92861

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Theorems.Thm_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
import Theorems.Thm_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_FormalGroup_coeff_one_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace QuotIsoAux

open MvPowerSeries

theorem vanish {S : Type*} [CommRing S] (q : ℕ) [Fact q.Prime] [CharP S q]
    {F G : FormalGroup S} (θ : FormalGroup.LawHom F G) (h1 : PowerSeries.coeff 1 θ.series = 0)
    (n : ℕ) (hn : ¬ q ∣ n) : PowerSeries.coeff n θ.series = 0 := by
  have hlin : MvFormalGroup.linearPart θ.toMvHom.toPowerSeries = 0 := by
    show MvFormalGroup.linearPart (fun _ : Fin 1 => MvFormalGroup.toMv θ.series) = 0
    rw [MvFormalGroup.linearPart_toMv, h1, zero_smul]
  have h := MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP q
    (MvFormalGroup.ofFormalGroup F) (MvFormalGroup.ofFormalGroup G) θ.toMvHom.toPowerSeries
    θ.toMvHom.constantCoeff_eq_zero hlin θ.toMvHom.subst_eq 0 (Finsupp.single 0 n)
    ⟨0, by rwa [Finsupp.single_eq_same]⟩
  rwa [FormalGroup.LawHom.toMvHom_toPowerSeries, MvFormalGroup.coeff_toMv] at h

section FibreProduct

variable {T k : Type*} [CommRing T] [CommRing k] (res : T →+* k)

noncomputable def FP : Subring (T × T) := RingHom.eqLocus (res.comp (RingHom.fst T T)) (res.comp (RingHom.snd T T))

theorem mem_FP {p : T × T} : p ∈ FP res ↔ res p.1 = res p.2 := Iff.rfl

noncomputable def π₁ : FP res →+* T := (RingHom.fst T T).comp (FP res).subtype
noncomputable def π₂ : FP res →+* T := (RingHom.snd T T).comp (FP res).subtype

@[scoped simp] theorem π₁_apply (p : FP res) : π₁ res p = p.1.1 := rfl
@[scoped simp] theorem π₂_apply (p : FP res) : π₂ res p = p.1.2 := rfl

theorem res_π₁_eq_res_π₂ (p : FP res) : res (π₁ res p) = res (π₂ res p) := p.2

noncomputable def pairS {σ : Type*} (f g : MvPowerSeries σ T) (h : MvPowerSeries.map res f = MvPowerSeries.map res g) :
    MvPowerSeries σ (FP res) := fun d =>
  ⟨(MvPowerSeries.coeff d f, MvPowerSeries.coeff d g), by
    show res (MvPowerSeries.coeff d f) = res (MvPowerSeries.coeff d g)
    rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]⟩

theorem map_π₁_pairS {σ : Type*} (f g : MvPowerSeries σ T) (h) : MvPowerSeries.map (π₁ res) (pairS res f g h) = f := by
  ext d; rw [MvPowerSeries.coeff_map]; rfl

theorem map_π₂_pairS {σ : Type*} (f g : MvPowerSeries σ T) (h) : MvPowerSeries.map (π₂ res) (pairS res f g h) = g := by
  ext d; rw [MvPowerSeries.coeff_map]; rfl

theorem jinj {σ : Type*} {a b : MvPowerSeries σ (FP res)}
    (h₁ : MvPowerSeries.map (π₁ res) a = MvPowerSeries.map (π₁ res) b)
    (h₂ : MvPowerSeries.map (π₂ res) a = MvPowerSeries.map (π₂ res) b) : a = b := by
  funext d
  apply Subtype.ext
  apply Prod.ext
  · have := congrArg (MvPowerSeries.coeff d) h₁
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this
    exact this
  · have := congrArg (MvPowerSeries.coeff d) h₂
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this
    exact this

noncomputable def pairLaw (G G' : FormalGroup T) (h : MvPowerSeries.map res G.toPowerSeries = MvPowerSeries.map res G'.toPowerSeries) :
    FormalGroup (FP res) where
  toPowerSeries := pairS res G.toPowerSeries G'.toPowerSeries h
  zero_constantCoeff := by
    apply Subtype.ext; apply Prod.ext
    · exact G.zero_constantCoeff
    · exact G'.zero_constantCoeff
  lin_coeff_X := by
    apply Subtype.ext; apply Prod.ext
    · exact G.lin_coeff_X
    · exact G'.lin_coeff_X
  lin_coeff_Y := by
    apply Subtype.ext; apply Prod.ext
    · exact G.lin_coeff_Y
    · exact G'.lin_coeff_Y
  assoc := by
    have c0 : MvPowerSeries.constantCoeff (pairS res G.toPowerSeries G'.toPowerSeries h) = 0 := by
      apply Subtype.ext; apply Prod.ext
      · exact G.zero_constantCoeff
      · exact G'.zero_constantCoeff
    have hin : ∀ (a b : Fin 3), MvPowerSeries.HasSubst
        (![X a, X b] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) := fun a b => HasSubst.X_X
    have cL : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) (FP res)), X 1]
        (pairS res G.toPowerSeries G'.toPowerSeries h)) = 0 :=
      constantCoeff_subst_eq_zero (hin 0 1) (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) c0
    have cR : MvPowerSeries.constantCoeff (MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) (FP res)), X 2]
        (pairS res G.toPowerSeries G'.toPowerSeries h)) = 0 :=
      constantCoeff_subst_eq_zero (hin 1 2) (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, constantCoeff_X _⟩) c0
    have hL : MvPowerSeries.HasSubst (![MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) (FP res)), X 1]
        (pairS res G.toPowerSeries G'.toPowerSeries h), X 2] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨cL, constantCoeff_X _⟩)
    have hR : MvPowerSeries.HasSubst (![X 0, MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) (FP res)), X 2]
        (pairS res G.toPowerSeries G'.toPowerSeries h)] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_X _, cR⟩)
    apply jinj res
    · rw [MvPowerSeries.map_subst hL, MvPowerSeries.map_subst hR, map_π₁_pairS]
      have e1 : (fun i : Fin 2 => MvPowerSeries.map (π₁ res) ((![MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) (FP res)), X 1]
          (pairS res G.toPowerSeries G'.toPowerSeries h), X 2] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) i)) =
          ![MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) T), X 1] G.toPowerSeries, X 2] := by
        funext i; fin_cases i
        · show MvPowerSeries.map (π₁ res) (MvPowerSeries.subst _ _) = _
          rw [MvPowerSeries.map_subst (hin 0 1), map_π₁_pairS]
          congr 1; funext j; fin_cases j <;> simp [MvPowerSeries.map_X]
        · show MvPowerSeries.map (π₁ res) (X 2) = X 2
          exact MvPowerSeries.map_X _ _
      have e2 : (fun i : Fin 2 => MvPowerSeries.map (π₁ res) ((![X 0, MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) (FP res)), X 2]
          (pairS res G.toPowerSeries G'.toPowerSeries h)] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) i)) =
          ![X 0, MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) T), X 2] G.toPowerSeries] := by
        funext i; fin_cases i
        · show MvPowerSeries.map (π₁ res) (X 0) = X 0
          exact MvPowerSeries.map_X _ _
        · show MvPowerSeries.map (π₁ res) (MvPowerSeries.subst _ _) = _
          rw [MvPowerSeries.map_subst (hin 1 2), map_π₁_pairS]
          congr 1; funext j; fin_cases j <;> simp [MvPowerSeries.map_X]
      rw [e1, e2]
      exact G.assoc
    · rw [MvPowerSeries.map_subst hL, MvPowerSeries.map_subst hR, map_π₂_pairS]
      have e1 : (fun i : Fin 2 => MvPowerSeries.map (π₂ res) ((![MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) (FP res)), X 1]
          (pairS res G.toPowerSeries G'.toPowerSeries h), X 2] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) i)) =
          ![MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) T), X 1] G'.toPowerSeries, X 2] := by
        funext i; fin_cases i
        · show MvPowerSeries.map (π₂ res) (MvPowerSeries.subst _ _) = _
          rw [MvPowerSeries.map_subst (hin 0 1), map_π₂_pairS]
          congr 1; funext j; fin_cases j <;> simp [MvPowerSeries.map_X]
        · show MvPowerSeries.map (π₂ res) (X 2) = X 2
          exact MvPowerSeries.map_X _ _
      have e2 : (fun i : Fin 2 => MvPowerSeries.map (π₂ res) ((![X 0, MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) (FP res)), X 2]
          (pairS res G.toPowerSeries G'.toPowerSeries h)] : Fin 2 → MvPowerSeries (Fin 3) (FP res)) i)) =
          ![X 0, MvPowerSeries.subst ![(X 1 : MvPowerSeries (Fin 3) T), X 2] G'.toPowerSeries] := by
        funext i; fin_cases i
        · show MvPowerSeries.map (π₂ res) (X 0) = X 0
          exact MvPowerSeries.map_X _ _
        · show MvPowerSeries.map (π₂ res) (MvPowerSeries.subst _ _) = _
          rw [MvPowerSeries.map_subst (hin 1 2), map_π₂_pairS]
          congr 1; funext j; fin_cases j <;> simp [MvPowerSeries.map_X]
      rw [e1, e2]
      exact G'.assoc

theorem pairLaw_bc₁ (G G' : FormalGroup T) (h) : (pairLaw res G G' h).IsBaseChange (π₁ res) G := by
  unfold FormalGroup.IsBaseChange; exact (map_π₁_pairS res _ _ h).symm

theorem pairLaw_bc₂ (G G' : FormalGroup T) (h) : (pairLaw res G G' h).IsBaseChange (π₂ res) G' := by
  unfold FormalGroup.IsBaseChange; exact (map_π₂_pairS res _ _ h).symm

theorem pairLaw_isComm (G G' : FormalGroup T) [G.IsComm] [G'.IsComm] (h) : (pairLaw res G G' h).IsComm := by
  refine ⟨?_⟩
  show pairS res G.toPowerSeries G'.toPowerSeries h =
    MvPowerSeries.subst ![X 1, X 0] (pairS res G.toPowerSeries G'.toPowerSeries h)
  have hv : ∀ (g : FP res →+* T), (fun i : Fin 2 => MvPowerSeries.map g ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) (FP res)) i)) =
      (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) T) := by
    intro g; funext i; fin_cases i <;> simp [MvPowerSeries.map_X]
  apply jinj res
  · rw [MvPowerSeries.map_subst HasSubst.X_X, map_π₁_pairS, hv]
    exact FormalGroup.IsComm.comm
  · rw [MvPowerSeries.map_subst HasSubst.X_X, map_π₂_pairS, hv]
    exact FormalGroup.IsComm.comm

end FibreProduct

end QuotIsoAux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot.QuotIsoAux"

namespace QuotIsoAux

open MvPowerSeries

section FibreProduct2

variable {T k : Type*} [CommRing T] [CommRing k] (res : T →+* k)

noncomputable def pairHom {G₁ G₁' G₂ G₂' : FormalGroup T} (h₁) (h₂)
    (θ : FormalGroup.LawHom G₁ G₂) (θ' : FormalGroup.LawHom G₁' G₂')
    (hθ : PowerSeries.map res θ.series = PowerSeries.map res θ'.series) :
    FormalGroup.LawHom (pairLaw res G₁ G₁' h₁) (pairLaw res G₂ G₂' h₂) where
  series := pairS res θ.series θ'.series hθ
  constantCoeff_series := by
    apply Subtype.ext; apply Prod.ext
    · exact θ.constantCoeff_series
    · exact θ'.constantCoeff_series
  comm := by
    have hs0 : PowerSeries.constantCoeff (pairS res θ.series θ'.series hθ : PowerSeries (FP res)) = 0 := by
      apply Subtype.ext; apply Prod.ext
      · exact θ.constantCoeff_series
      · exact θ'.constantCoeff_series
    have hF : PowerSeries.HasSubst (pairLaw res G₁ G₁' h₁).toPowerSeries :=
      PowerSeries.HasSubst.of_constantCoeff_zero (pairLaw res G₁ G₁' h₁).zero_constantCoeff
    have hXi : ∀ i : Fin 2, PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) (FP res)) := fun i =>
      PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
    have hsX : ∀ i : Fin 2, MvPowerSeries.constantCoeff
        (FormalGroup.LawHom.substX i (pairS res θ.series θ'.series hθ : PowerSeries (FP res))) = 0 := by
      intro i; unfold FormalGroup.LawHom.substX
      exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ hs0
    have hS : MvPowerSeries.HasSubst (![FormalGroup.LawHom.substX 0 (pairS res θ.series θ'.series hθ : PowerSeries (FP res)),
        FormalGroup.LawHom.substX 1 (pairS res θ.series θ'.series hθ : PowerSeries (FP res))] :
        Fin 2 → MvPowerSeries (Fin 2) (FP res)) :=
      hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hsX 0, hsX 1⟩)

    have key : ∀ (g : FP res →+* T) (Ga Gb : FormalGroup T) (η : FormalGroup.LawHom Ga Gb),
        MvPowerSeries.map g (pairLaw res G₁ G₁' h₁).toPowerSeries = Ga.toPowerSeries →
        MvPowerSeries.map g (pairLaw res G₂ G₂' h₂).toPowerSeries = Gb.toPowerSeries →
        MvPowerSeries.map g (pairS res θ.series θ'.series hθ) = η.series →
        MvPowerSeries.map g (PowerSeries.subst (pairLaw res G₁ G₁' h₁).toPowerSeries
            (pairS res θ.series θ'.series hθ : PowerSeries (FP res))) =
          MvPowerSeries.map g (MvPowerSeries.subst
            ![FormalGroup.LawHom.substX 0 (pairS res θ.series θ'.series hθ : PowerSeries (FP res)),
              FormalGroup.LawHom.substX 1 (pairS res θ.series θ'.series hθ : PowerSeries (FP res))]
            (pairLaw res G₂ G₂' h₂).toPowerSeries) := by
      intro g Ga Gb η e1 e2 e3
      have e3' : PowerSeries.map g (pairS res θ.series θ'.series hθ : PowerSeries (FP res)) = η.series := e3
      have hv : (fun i : Fin 2 => MvPowerSeries.map g
          ((![FormalGroup.LawHom.substX 0 (pairS res θ.series θ'.series hθ : PowerSeries (FP res)),
              FormalGroup.LawHom.substX 1 (pairS res θ.series θ'.series hθ : PowerSeries (FP res))] :
              Fin 2 → MvPowerSeries (Fin 2) (FP res)) i)) =
          ![FormalGroup.LawHom.substX 0 η.series, FormalGroup.LawHom.substX 1 η.series] := by
        funext i
        fin_cases i
        · show MvPowerSeries.map g (FormalGroup.LawHom.substX 0 (pairS res θ.series θ'.series hθ : PowerSeries (FP res))) =
            FormalGroup.LawHom.substX 0 η.series
          unfold FormalGroup.LawHom.substX
          rw [PowerSeries.map_subst (hXi _), MvPowerSeries.map_X, e3']
        · show MvPowerSeries.map g (FormalGroup.LawHom.substX 1 (pairS res θ.series θ'.series hθ : PowerSeries (FP res))) =
            FormalGroup.LawHom.substX 1 η.series
          unfold FormalGroup.LawHom.substX
          rw [PowerSeries.map_subst (hXi _), MvPowerSeries.map_X, e3']
      rw [PowerSeries.map_subst hF, e1, e3', η.comm, MvPowerSeries.map_subst hS, e2, hv]
    apply jinj res
    · exact key (π₁ res) G₁ G₂ θ (map_π₁_pairS res _ _ h₁) (map_π₁_pairS res _ _ h₂) (map_π₁_pairS res _ _ hθ)
    · exact key (π₂ res) G₁' G₂' θ' (map_π₂_pairS res _ _ h₁) (map_π₂_pairS res _ _ h₂) (map_π₂_pairS res _ _ hθ)

@[scoped simp] theorem pairHom_series {G₁ G₁' G₂ G₂' : FormalGroup T} (h₁) (h₂)
    (θ : FormalGroup.LawHom G₁ G₂) (θ' : FormalGroup.LawHom G₁' G₂') (hθ) :
    (pairHom res h₁ h₂ θ θ' hθ).series = pairS res θ.series θ'.series hθ := rfl

noncomputable def tauMinus (s : k →+* T) (hs : ∀ a, res (s a) = a) (hmm : ∀ v w : T, res v = 0 → res w = 0 → v * w = 0) :
    FP res →+* T where
  toFun p := p.1.1 - p.1.2 + s (res p.1.2)
  map_one' := by simp
  map_zero' := by simp
  map_add' p p' := by
    simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, map_add]; ring
  map_mul' p p' := by
    simp only [Subring.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    have hp : res p.1.1 = res p.1.2 := p.2
    have hp' : res p'.1.1 = res p'.1.2 := p'.2
    have mv : res (p.1.1 - s (res p.1.2)) = 0 := by rw [map_sub, hs, hp, sub_self]
    have mw : res (p.1.2 - s (res p.1.2)) = 0 := by rw [map_sub, hs, sub_self]
    have mv' : res (p'.1.1 - s (res p'.1.2)) = 0 := by rw [map_sub, hs, hp', sub_self]
    have mw' : res (p'.1.2 - s (res p'.1.2)) = 0 := by rw [map_sub, hs, sub_self]
    have h1 := hmm _ _ mv mw'
    have h2 := hmm _ _ mw mv'
    have h3 := hmm _ _ mw mw'
    linear_combination h1 + h2 - 2 * h3

@[scoped simp] theorem tauMinus_apply (s : k →+* T) (hs) (hmm) (p : FP res) :
    tauMinus res s hs hmm p = p.1.1 - p.1.2 + s (res p.1.2) := rfl

noncomputable def tauPlus (s : k →+* T) (hs : ∀ a, res (s a) = a) (hmm : ∀ v w : T, res v = 0 → res w = 0 → v * w = 0) :
    FP res →+* T where
  toFun p := p.1.1 + p.1.2 - s (res p.1.2)
  map_one' := by simp
  map_zero' := by simp
  map_add' p p' := by
    simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, map_add]; ring
  map_mul' p p' := by
    simp only [Subring.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    have hp : res p.1.1 = res p.1.2 := p.2
    have hp' : res p'.1.1 = res p'.1.2 := p'.2
    have mv : res (p.1.1 - s (res p.1.2)) = 0 := by rw [map_sub, hs, hp, sub_self]
    have mw : res (p.1.2 - s (res p.1.2)) = 0 := by rw [map_sub, hs, sub_self]
    have mv' : res (p'.1.1 - s (res p'.1.2)) = 0 := by rw [map_sub, hs, hp', sub_self]
    have mw' : res (p'.1.2 - s (res p'.1.2)) = 0 := by rw [map_sub, hs, sub_self]
    have h1 := hmm _ _ mv mw'
    have h2 := hmm _ _ mw mv'
    linear_combination (-1 : T) * h1 - h2

@[scoped simp] theorem tauPlus_apply (s : k →+* T) (hs) (hmm) (p : FP res) :
    tauPlus res s hs hmm p = p.1.1 + p.1.2 - s (res p.1.2) := rfl

end FibreProduct2
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot.QuotIsoAux"

noncomputable def idHom {R : Type*} [CommRing R] (G : FormalGroup R) : FormalGroup.LawHom G G where
  series := PowerSeries.X
  constantCoeff_series := PowerSeries.constantCoeff_X
  comm := by
    have hF : PowerSeries.HasSubst G.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
    have hsx : ∀ i : Fin 2, FormalGroup.LawHom.substX i (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
      intro i; unfold FormalGroup.LawHom.substX
      exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))
    have hvec : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = MvPowerSeries.X := by
      funext i; fin_cases i <;> rfl
    rw [PowerSeries.subst_X hF, hsx, hsx, hvec, MvPowerSeries.subst_self, id]

@[scoped simp] theorem idHom_series {R : Type*} [CommRing R] (G : FormalGroup R) : (idHom G).series = PowerSeries.X := rfl

end QuotIsoAux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot.QuotIsoAux"

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra k T]
    (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hres : ∀ a : k, resT (algebraMap k T a) = a) (hker : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) [G.IsComm] [G'.IsComm] (hG : G.IsBaseChange resT F₀) (hG' : G'.IsBaseChange resT F₀)
    (hc : PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q)) :
    ∃ ψ : FormalGroup.LawIso G G', ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  haveI hIT : IsAdicComplete (maximalIdeal T) T := by
    have hpow : ∀ n, 2 ≤ n → (maximalIdeal T ^ n • ⊤ : Submodule T T) = ⊥ := by
      intro n hn
      have : maximalIdeal T ^ n = ⊥ := le_bot_iff.mp (hsq ▸ Ideal.pow_le_pow_right hn)
      rw [this]; simp
    haveI : IsHausdorff (maximalIdeal T) T := ⟨fun x hx => by
      have := hx 2
      rw [hpow 2 le_rfl, SModEq.bot] at this
      exact this⟩
    haveI : IsPrecomplete (maximalIdeal T) T := ⟨fun f hf => by
      refine ⟨f 2, fun n => ?_⟩
      rcases le_or_gt n 2 with hn | hn
      · exact (hf hn)
      · have h2 := hf hn.le
        rw [hpow 2 le_rfl, SModEq.bot] at h2
        rw [h2]⟩
    exact ⟨⟩
  haveI : Nontrivial T := inferInstance
  haveI : CharP T q := charP_of_injective_algebraMap (algebraMap k T).injective q
  have hqT : (q : T) = 0 := CharP.cast_eq_zero T q
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hker, RingHom.mem_ker]
  have hmm : ∀ v w : T, resT v = 0 → resT w = 0 → v * w = 0 := by
    intro v w hv hw
    have : v * w ∈ maximalIdeal T ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ((hmem v).mpr hv) ((hmem w).mpr hw)
    rwa [hsq, Ideal.mem_bot] at this
  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hqF₀⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀
  have hqlt : q < q * q := by nlinarith

  have eG : MvPowerSeries.map resT G.toPowerSeries = F₀.toPowerSeries := hG.symm
  have eG' : MvPowerSeries.map resT G'.toPowerSeries = F₀.toPowerSeries := hG'.symm
  have hGG' : MvPowerSeries.map resT G.toPowerSeries = MvPowerSeries.map resT G'.toPowerSeries := by rw [eG, eG']

  haveI : (QuotIsoAux.pairLaw resT G G' hGG').IsComm := QuotIsoAux.pairLaw_isComm resT G G' hGG'
  set G₂ : FormalGroup T := (QuotIsoAux.pairLaw resT G G' hGG').map
    (QuotIsoAux.tauMinus resT (algebraMap k T) hres hmm) with hG₂def
  have hbcG₂ : (QuotIsoAux.pairLaw resT G G' hGG').IsBaseChange
      (QuotIsoAux.tauMinus resT (algebraMap k T) hres hmm) G₂ := by rw [hG₂def]; rfl
  haveI : G₂.IsComm := FormalGroup.IsBaseChange.isComm _ _ _ hbcG₂
  have hcoeffG₂ : ∀ d, MvPowerSeries.coeff d G₂.toPowerSeries =
      MvPowerSeries.coeff d G.toPowerSeries - MvPowerSeries.coeff d G'.toPowerSeries +
        algebraMap k T (resT (MvPowerSeries.coeff d G'.toPowerSeries)) := by
    intro d; rw [hG₂def, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]; rfl
  have hG₂ : G₂.IsBaseChange resT F₀ := by
    unfold FormalGroup.IsBaseChange
    ext d
    rw [MvPowerSeries.coeff_map, hcoeffG₂, map_add, map_sub, hres, sub_add_cancel, ← MvPowerSeries.coeff_map, eG]

  have hc' : resT (PowerSeries.coeff q (G'.nthSeries q)) = 0 := by
    rw [← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map G' resT F₀ hG' q, hqF₀,
      PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt)]
  have hc₂ : PowerSeries.coeff q (G₂.nthSeries q) = 0 := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map _ _ G₂ hbcG₂ q, PowerSeries.coeff_map]
    have e1 : (PowerSeries.coeff q ((QuotIsoAux.pairLaw resT G G' hGG').nthSeries q)).1.1 =
        PowerSeries.coeff q (G.nthSeries q) := by
      show QuotIsoAux.π₁ resT (PowerSeries.coeff q ((QuotIsoAux.pairLaw resT G G' hGG').nthSeries q)) = _
      rw [← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map _ _ G (QuotIsoAux.pairLaw_bc₁ resT G G' hGG') q]
    have e2 : (PowerSeries.coeff q ((QuotIsoAux.pairLaw resT G G' hGG').nthSeries q)).1.2 =
        PowerSeries.coeff q (G'.nthSeries q) := by
      show QuotIsoAux.π₂ resT (PowerSeries.coeff q ((QuotIsoAux.pairLaw resT G G' hGG').nthSeries q)) = _
      rw [← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map _ _ G' (QuotIsoAux.pairLaw_bc₂ resT G G' hGG') q]
    rw [QuotIsoAux.tauMinus_apply, e1, e2, hc, hc', map_zero, sub_self, _root_.zero_add]

  obtain ⟨θ, hθ⟩ := FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot resT
    (by rw [hker]; exact hsq) q hqT F₀ G₂ G₂ hG₂ hG₂
  have h1 : PowerSeries.coeff 1 θ.series = 0 := by rw [hθ, FormalGroup.coeff_one_nthSeries, hqT]
  have van1 := QuotIsoAux.vanish q θ h1
  obtain ⟨θ₁, hθ₁⟩ := FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero q θ h1
  have h1' : PowerSeries.coeff 1 θ₁.series = 0 := by rw [hθ₁, mul_one, hθ, hc₂]
  have van2 := QuotIsoAux.vanish q θ₁ h1'
  have hvan : ∀ d, d < q * q → PowerSeries.coeff d (G₂.nthSeries q) = 0 := by
    intro d hd
    by_cases hqd : q ∣ d
    · obtain ⟨n, rfl⟩ := hqd
      by_cases hqn : q ∣ n
      · obtain ⟨m, rfl⟩ := hqn
        have hm : m = 0 := by
          by_contra hm
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          nlinarith
        subst hm
        rw [mul_zero, mul_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact G₂.constantCoeff_nthSeries q
      · rw [← hθ, ← hθ₁]; exact van2 n hqn
    · rw [← hθ]; exact van1 d hqd
  have hD₂ : G₂.IsDrinfeldBasisAdic (maximalIdeal T) q 0 0 := by
    rw [FormalGroup.isDrinfeldBasisAdic_zero_zero_iff]
    refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + q * q) (G₂.nthSeries q), ?_, ?_⟩
    · rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
        _root_.zero_add]
      by_contra hnu
      have hm : PowerSeries.coeff (q * q) (G₂.nthSeries q) ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmem, ← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map G₂ resT F₀ hG₂ q, hqF₀,
        PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hm
      exact (PowerSeries.isUnit_iff_constantCoeff.mp hu₀).ne_zero hm
    · ext d
      rw [PowerSeries.coeff_mul_X_pow']
      split_ifs with h
      · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel h]
      · exact hvan d (not_le.mp h)

  obtain ⟨ψ₀, hψ₀⟩ := FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm q k F₀ hF₀
    T hsq resT hres hker G₂ hG₂ hD₂ (F₀.map (algebraMap k T)) rfl

  have hcomp : resT.comp (algebraMap k T) = RingHom.id k := RingHom.ext hres
  have eG₀ : MvPowerSeries.map resT (F₀.map (algebraMap k T)).toPowerSeries = F₀.toPowerSeries := by
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.map_map, hcomp, MvPowerSeries.map_id]; rfl
  have hG'G₀ : MvPowerSeries.map resT G'.toPowerSeries = MvPowerSeries.map resT (F₀.map (algebraMap k T)).toPowerSeries := by
    rw [eG', eG₀]
  have hG'G₂ : MvPowerSeries.map resT G'.toPowerSeries = MvPowerSeries.map resT G₂.toPowerSeries := by
    rw [eG', show MvPowerSeries.map resT G₂.toPowerSeries = F₀.toPowerSeries from hG₂.symm]
  have hXψ : PowerSeries.map resT (QuotIsoAux.idHom G').series = PowerSeries.map resT ψ₀.series := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, QuotIsoAux.idHom_series, PowerSeries.coeff_X,
      show PowerSeries.coeff m ψ₀.toLawHom.series = PowerSeries.coeff m ψ₀.series from rfl, hψ₀ m]
    split_ifs <;> simp
  have hbc1 : (QuotIsoAux.pairLaw resT G' (F₀.map (algebraMap k T)) hG'G₀).IsBaseChange
      (QuotIsoAux.tauPlus resT (algebraMap k T) hres hmm) G' := by
    unfold FormalGroup.IsBaseChange
    ext d
    rw [MvPowerSeries.coeff_map, QuotIsoAux.tauPlus_apply]
    show MvPowerSeries.coeff d G'.toPowerSeries = MvPowerSeries.coeff d G'.toPowerSeries +
      MvPowerSeries.coeff d (F₀.map (algebraMap k T)).toPowerSeries -
        algebraMap k T (resT (MvPowerSeries.coeff d (F₀.map (algebraMap k T)).toPowerSeries))
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map, hres, add_sub_cancel_right]
  have hbc2 : (QuotIsoAux.pairLaw resT G' G₂ hG'G₂).IsBaseChange
      (QuotIsoAux.tauPlus resT (algebraMap k T) hres hmm) G := by
    unfold FormalGroup.IsBaseChange
    ext d
    rw [MvPowerSeries.coeff_map, QuotIsoAux.tauPlus_apply]
    show MvPowerSeries.coeff d G.toPowerSeries = MvPowerSeries.coeff d G'.toPowerSeries +
      MvPowerSeries.coeff d G₂.toPowerSeries - algebraMap k T (resT (MvPowerSeries.coeff d G₂.toPowerSeries))
    have hrr : resT (MvPowerSeries.coeff d G.toPowerSeries) = resT (MvPowerSeries.coeff d G'.toPowerSeries) := by
      rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hGG']
    rw [hcoeffG₂, map_add, map_sub, hres, hrr, sub_add_cancel]
    ring
  obtain ⟨κ, hκ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map
    (QuotIsoAux.tauPlus resT (algebraMap k T) hres hmm)
    (QuotIsoAux.pairHom resT hG'G₀ hG'G₂ (QuotIsoAux.idHom G') ψ₀.toLawHom hXψ) G' G hbc1 hbc2
  have hκs : κ.series = ψ₀.series := by
    rw [hκ]
    ext d
    rw [PowerSeries.coeff_map, QuotIsoAux.pairHom_series]
    show QuotIsoAux.tauPlus resT (algebraMap k T) hres hmm
      (PowerSeries.coeff d (QuotIsoAux.pairS resT (QuotIsoAux.idHom G').series ψ₀.toLawHom.series hXψ)) = _
    rw [QuotIsoAux.tauPlus_apply]
    show PowerSeries.coeff d (PowerSeries.X : PowerSeries T) + PowerSeries.coeff d ψ₀.series -
      algebraMap k T (resT (PowerSeries.coeff d ψ₀.series)) = PowerSeries.coeff d ψ₀.series
    rw [hψ₀ d, PowerSeries.coeff_X]
    split_ifs <;> simp
  have hκu : IsUnit (PowerSeries.coeff 1 κ.series) := by rw [hκs]; exact ψ₀.isUnit_coeff_one
  obtain ⟨κ', h1', -⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X (⟨κ, hκu⟩ : FormalGroup.LawIso G' G)
  refine ⟨κ', fun m => ?_⟩

  have hsK : PowerSeries.HasSubst κ.series := PowerSeries.HasSubst.of_constantCoeff_zero' κ.constantCoeff_series
  have em : ∀ p : PowerSeries T, MvPowerSeries.map resT p = PowerSeries.map resT p := fun _ => rfl
  have hredκ : PowerSeries.map resT κ.series = PowerSeries.X := by
    rw [hκs]; ext n; rw [PowerSeries.coeff_map, hψ₀ n, PowerSeries.coeff_X]
  have h1'' : PowerSeries.subst κ.series κ'.series = PowerSeries.X := h1'
  have e := congrArg (MvPowerSeries.map resT) h1''
  rw [PowerSeries.map_subst hsK, em, em, hredκ, PowerSeries.X_subst, PowerSeries.map_X] at e
  have e' : PowerSeries.map resT κ'.series = PowerSeries.X := e
  rw [← PowerSeries.coeff_map, show PowerSeries.map resT κ'.toLawHom.series = PowerSeries.X from e', PowerSeries.coeff_X]

end S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
end P2MW
export P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot (solution)
