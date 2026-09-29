-- Prove2me | solution 1 for FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/50b219d2-87cf-54cd-affc-52c408da157a

import Mathlib
import Theorems.Thm_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace L3Aux

open MvPowerSeries

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

section SmallExt

variable {T : Type*} [CommRing T] (I : Ideal T)

noncomputable def U' : Subring (TrivSqZeroExt T T) where
  carrier := {u | u.snd ∈ I}
  mul_mem' := by
    intro a b ha hb
    show (a * b).snd ∈ I
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact I.add_mem (I.mul_mem_left _ hb) (I.mul_mem_right _ ha)
  one_mem' := by show (1 : TrivSqZeroExt T T).snd ∈ I; rw [TrivSqZeroExt.snd_one]; exact I.zero_mem
  add_mem' := by
    intro a b ha hb; show (a + b).snd ∈ I; rw [TrivSqZeroExt.snd_add]; exact I.add_mem ha hb
  zero_mem' := by show (0 : TrivSqZeroExt T T).snd ∈ I; rw [TrivSqZeroExt.snd_zero]; exact I.zero_mem
  neg_mem' := by intro a ha; show (-a).snd ∈ I; rw [TrivSqZeroExt.snd_neg]; exact I.neg_mem ha

theorem U'_ext {a b : U' I} (h1 : a.1.fst = b.1.fst) (h2 : a.1.snd = b.1.snd) : a = b :=
  Subtype.ext (TrivSqZeroExt.ext h1 h2)

noncomputable def mkU (x s : T) (hs : s ∈ I) : U' I := ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr s, by
  show (TrivSqZeroExt.inl x + TrivSqZeroExt.inr s : TrivSqZeroExt T T).snd ∈ I
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add]; exact hs⟩

@[scoped simp] theorem fst_mkU (x s : T) (hs : s ∈ I) : (mkU I x s hs).1.fst = x := by
  show (TrivSqZeroExt.inl x + TrivSqZeroExt.inr s : TrivSqZeroExt T T).fst = x
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]

@[scoped simp] theorem snd_mkU (x s : T) (hs : s ∈ I) : (mkU I x s hs).1.snd = s := by
  show (TrivSqZeroExt.inl x + TrivSqZeroExt.inr s : TrivSqZeroExt T T).snd = s
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add]

@[scoped simp] theorem fst_mul_U (a b : U' I) : (a * b).1.fst = a.1.fst * b.1.fst := TrivSqZeroExt.fst_mul a.1 b.1
@[scoped simp] theorem snd_mul_U (a b : U' I) : (a * b).1.snd = a.1.fst * b.1.snd + b.1.fst * a.1.snd := by
  show (a.1 * b.1).snd = _
  rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_comm a.1.snd]
@[scoped simp] theorem fst_add_U (a b : U' I) : (a + b).1.fst = a.1.fst + b.1.fst := TrivSqZeroExt.fst_add a.1 b.1
@[scoped simp] theorem snd_add_U (a b : U' I) : (a + b).1.snd = a.1.snd + b.1.snd := TrivSqZeroExt.snd_add a.1 b.1
@[scoped simp] theorem fst_one_U : (1 : U' I).1.fst = 1 := TrivSqZeroExt.fst_one
@[scoped simp] theorem snd_one_U : (1 : U' I).1.snd = 0 := TrivSqZeroExt.snd_one
@[scoped simp] theorem fst_zero_U : (0 : U' I).1.fst = 0 := TrivSqZeroExt.fst_zero
@[scoped simp] theorem snd_zero_U : (0 : U' I).1.snd = 0 := TrivSqZeroExt.snd_zero
@[scoped simp] theorem fst_sub_U (a b : U' I) : (a - b).1.fst = a.1.fst - b.1.fst := TrivSqZeroExt.fst_sub a.1 b.1
@[scoped simp] theorem snd_sub_U (a b : U' I) : (a - b).1.snd = a.1.snd - b.1.snd := TrivSqZeroExt.snd_sub a.1 b.1

noncomputable def fstU : U' I →+* T := (TrivSqZeroExt.fstHom T T T).toRingHom.comp (U' I).subtype

@[scoped simp] theorem fstU_apply (a : U' I) : fstU I a = a.1.fst := rfl

noncomputable def inlU : T →+* U' I where
  toFun x := mkU I x 0 I.zero_mem
  map_one' := by apply U'_ext I <;> simp
  map_mul' x y := by apply U'_ext I <;> simp
  map_zero' := by apply U'_ext I <;> simp
  map_add' x y := by apply U'_ext I <;> simp

@[scoped simp] theorem fst_inlU (x : T) : (inlU I x).1.fst = x := fst_mkU I x 0 I.zero_mem
@[scoped simp] theorem snd_inlU (x : T) : (inlU I x).1.snd = 0 := snd_mkU I x 0 I.zero_mem

theorem mul_mem_zero (hII : I * I = ⊥) {a b : T} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have : a * b ∈ I * I := Ideal.mul_mem_mul ha hb
  rwa [hII, Ideal.mem_bot] at this

noncomputable def σU (hII : I * I = ⊥) : U' I →+* T where
  toFun a := a.1.fst + a.1.snd
  map_one' := by simp
  map_mul' a b := by
    have h := mul_mem_zero I hII a.2 b.2
    simp only [fst_mul_U, snd_mul_U]
    linear_combination (-1 : T) * h
  map_zero' := by simp
  map_add' a b := by simp only [fst_add_U, snd_add_U]; ring

@[scoped simp] theorem σU_apply (hII : I * I = ⊥) (a : U' I) : σU I hII a = a.1.fst + a.1.snd := rfl

theorem mem_of_FP (p : FP (Ideal.Quotient.mk I)) : p.1.2 - p.1.1 ∈ I := by
  rw [← neg_sub]; exact I.neg_mem ((Ideal.Quotient.eq).mp p.2)

noncomputable def θU (hII : I * I = ⊥) : FP (Ideal.Quotient.mk I) →+* U' I where
  toFun p := mkU I p.1.1 (p.1.2 - p.1.1) (mem_of_FP I p)
  map_one' := by apply U'_ext I <;> simp
  map_mul' p p' := by
    have h := mul_mem_zero I hII (mem_of_FP I p) (mem_of_FP I p')
    apply U'_ext I
    · simp
    · simp only [snd_mkU, snd_mul_U, fst_mkU]
      show p.1.2 * p'.1.2 - p.1.1 * p'.1.1 = _
      linear_combination h
  map_zero' := by apply U'_ext I <;> simp
  map_add' p p' := by
    apply U'_ext I
    · simp
    · simp only [snd_mkU, snd_add_U]
      show p.1.2 + p'.1.2 - (p.1.1 + p'.1.1) = _
      ring

@[scoped simp] theorem fst_θU (hII : I * I = ⊥) (p : FP (Ideal.Quotient.mk I)) : (θU I hII p).1.fst = p.1.1 := fst_mkU I _ _ (mem_of_FP I p)
@[scoped simp] theorem snd_θU (hII : I * I = ⊥) (p : FP (Ideal.Quotient.mk I)) : (θU I hII p).1.snd = p.1.2 - p.1.1 :=
  snd_mkU I _ _ (mem_of_FP I p)

theorem fstU_comp_θU (hII : I * I = ⊥) : (fstU I).comp (θU I hII) = π₁ (Ideal.Quotient.mk I) :=
  RingHom.ext fun p => fst_θU I hII p
theorem σU_comp_θU (hII : I * I = ⊥) : (σU I hII).comp (θU I hII) = π₂ (Ideal.Quotient.mk I) :=
  RingHom.ext fun p => by
    show (θU I hII p).1.fst + (θU I hII p).1.snd = p.1.2
    rw [fst_θU, snd_θU]; ring
theorem fstU_comp_inlU : (fstU I).comp (inlU I) = RingHom.id T := RingHom.ext fun x => fst_inlU I x
theorem σU_comp_inlU (hII : I * I = ⊥) : (σU I hII).comp (inlU I) = RingHom.id T := RingHom.ext fun x => by
  show (inlU I x).1.fst + (inlU I x).1.snd = x
  rw [fst_inlU, snd_inlU, _root_.add_zero]

end SmallExt

end L3Aux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

namespace L3Aux

section Thickening

variable {T : Type*} [CommRing T] [IsLocalRing T] (I : Ideal T) (hIm : I * IsLocalRing.maximalIdeal T = ⊥)

theorem isUnit_of_isUnit_fst (a : U' I) (h : IsUnit a.1.fst) : IsUnit a := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  refine isUnit_iff_exists_inv.mpr ⟨mkU I v (-(v * v * a.1.snd)) (I.neg_mem (I.mul_mem_left _ a.2)), ?_⟩
  apply U'_ext I
  · rw [fst_mul_U, fst_mkU, hv, fst_one_U]
  · rw [snd_mul_U, fst_mkU, snd_mkU, snd_one_U]
    linear_combination (-(v * a.1.snd)) * hv

scoped instance instIsLocalRingU' : IsLocalRing (U' I) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases h : IsUnit a.1.fst
  · exact Or.inl (isUnit_of_isUnit_fst I a h)
  · right
    apply isUnit_of_isUnit_fst I
    rw [fst_sub_U, fst_one_U]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mpr h)

noncomputable def J : Ideal (U' I) where
  carrier := {u | u.1.fst ∈ IsLocalRing.maximalIdeal T ∧ u.1.snd = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [fst_add_U]; exact Ideal.add_mem _ ha1 hb1, by rw [snd_add_U, ha2, hb2, _root_.add_zero]⟩
  zero_mem' := ⟨by rw [fst_zero_U]; exact Ideal.zero_mem _, snd_zero_U I⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    refine ⟨by rw [smul_eq_mul, fst_mul_U]; exact Ideal.mul_mem_left _ _ hu1, ?_⟩
    rw [smul_eq_mul, snd_mul_U, hu2, mul_zero, _root_.zero_add]
    have : c.1.snd * u.1.fst ∈ I * IsLocalRing.maximalIdeal T := Ideal.mul_mem_mul c.2 hu1
    rw [hIm, Ideal.mem_bot] at this
    rw [mul_comm]; exact this

theorem mem_J {u : U' I} : u ∈ J I hIm ↔ u.1.fst ∈ IsLocalRing.maximalIdeal T ∧ u.1.snd = 0 := Iff.rfl

theorem J_ne_top : J I hIm ≠ ⊤ := by
  intro h
  have : (1 : U' I) ∈ J I hIm := h ▸ Submodule.mem_top
  rw [mem_J, fst_one_U] at this
  exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top ((Ideal.eq_top_iff_one _).mpr this.1)

end Thickening
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

end L3Aux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

namespace L3Aux

section Tpp

variable {T : Type*} [CommRing T] [IsLocalRing T] (I : Ideal T) (hIm : I * IsLocalRing.maximalIdeal T = ⊥)
variable {k : Type*} [Field k] (resT : T →+* k) (hresT : Function.Surjective resT)
  (hkerT : RingHom.ker resT = IsLocalRing.maximalIdeal T)

abbrev Tpp : Type _ := U' I ⧸ J I hIm

scoped instance : Nontrivial (Tpp I hIm) := Ideal.Quotient.nontrivial_iff.mpr (J_ne_top I hIm)

scoped instance instIsLocalRingTpp : IsLocalRing (Tpp I hIm) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (J I hIm)) Ideal.Quotient.mk_surjective

include hkerT in
theorem J_le_ker : ∀ u ∈ J I hIm, (resT.comp (fstU I)) u = 0 := by
  intro u hu
  rw [mem_J] at hu
  show resT u.1.fst = 0
  rw [← RingHom.mem_ker, hkerT]; exact hu.1

noncomputable def resPP : Tpp I hIm →+* k := Ideal.Quotient.lift (J I hIm) (resT.comp (fstU I)) (J_le_ker I hIm resT hkerT)

@[scoped simp] theorem resPP_mk (u : U' I) : resPP I hIm resT hkerT (Ideal.Quotient.mk (J I hIm) u) = resT u.1.fst :=
  Ideal.Quotient.lift_mk _ _ _

include hkerT in
theorem ker_le_inl : ∀ x ∈ RingHom.ker resT, ((Ideal.Quotient.mk (J I hIm)).comp (inlU I)) x = 0 := by
  intro x hx
  show Ideal.Quotient.mk (J I hIm) (inlU I x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_J, fst_inlU, snd_inlU, ← hkerT]
  exact ⟨hx, rfl⟩

noncomputable def secPP : k →+* Tpp I hIm :=
  (Ideal.Quotient.lift (RingHom.ker resT) ((Ideal.Quotient.mk (J I hIm)).comp (inlU I)) (ker_le_inl I hIm resT hkerT)).comp
    (RingHom.quotientKerEquivOfSurjective hresT).symm.toRingHom

theorem secPP_resT (t : T) : secPP I hIm resT hresT hkerT (resT t) = Ideal.Quotient.mk (J I hIm) (inlU I t) := by
  unfold secPP
  rw [RingHom.comp_apply]
  have : (RingHom.quotientKerEquivOfSurjective hresT).symm.toRingHom (resT t) = Ideal.Quotient.mk (RingHom.ker resT) t := by
    apply (RingHom.quotientKerEquivOfSurjective hresT).injective
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rfl
  rw [this, Ideal.Quotient.lift_mk]
  rfl

theorem resPP_secPP (a : k) : resPP I hIm resT hkerT (secPP I hIm resT hresT hkerT a) = a := by
  obtain ⟨t, rfl⟩ := hresT a
  rw [secPP_resT, resPP_mk, fst_inlU]

include hresT in
theorem resPP_surjective : Function.Surjective (resPP I hIm resT hkerT) := fun a =>
  ⟨secPP I hIm resT hresT hkerT a, resPP_secPP I hIm resT hresT hkerT a⟩

include hresT in
theorem ker_resPP : RingHom.ker (resPP I hIm resT hkerT) = IsLocalRing.maximalIdeal (Tpp I hIm) :=
  IsLocalRing.eq_maximalIdeal (R := Tpp I hIm)
    (RingHom.ker_isMaximal_of_surjective (resPP I hIm resT hkerT) (resPP_surjective I hIm resT hresT hkerT))

include resT hresT hkerT in

theorem maximalIdeal_sq : IsLocalRing.maximalIdeal (Tpp I hIm) ^ 2 = ⊥ := by
  rw [← ker_resPP I hIm resT hresT hkerT, pow_two, ← le_bot_iff, Ideal.mul_le]
  intro a ha b hb
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [RingHom.mem_ker, resPP_mk, ← RingHom.mem_ker, hkerT] at ha hb
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_J, fst_mul_U, snd_mul_U]
  refine ⟨Ideal.mul_mem_left _ _ hb, ?_⟩
  have h1 : v.1.snd * u.1.fst = 0 := by
    have : v.1.snd * u.1.fst ∈ I * IsLocalRing.maximalIdeal T := Ideal.mul_mem_mul v.2 ha
    rwa [hIm, Ideal.mem_bot] at this
  have h2 : u.1.snd * v.1.fst = 0 := by
    have : u.1.snd * v.1.fst ∈ I * IsLocalRing.maximalIdeal T := Ideal.mul_mem_mul u.2 hb
    rwa [hIm, Ideal.mem_bot] at this
  linear_combination h1 + h2

include resT hresT hkerT in
theorem resPP_mul_eq_zero (a b : Tpp I hIm) (ha : resPP I hIm resT hkerT a = 0) (hb : resPP I hIm resT hkerT b = 0) :
    a * b = 0 := by
  have h := maximalIdeal_sq I hIm resT hresT hkerT
  rw [← ker_resPP I hIm resT hresT hkerT, pow_two, ← le_bot_iff, Ideal.mul_le] at h
  exact (Ideal.mem_bot).mp (h a ((RingHom.mem_ker).mpr ha) b ((RingHom.mem_ker).mpr hb))

end Tpp
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

end L3Aux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

namespace L3Aux

theorem isComm_map {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) [hF : F.IsComm] (f : R →+* S) :
    (F.map f).IsComm := by
  constructor
  show (F.map f).toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (F.map f).toPowerSeries
  have h : F.toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] F.toPowerSeries := hF.comm
  have hswap : (fun i => MvPowerSeries.map f
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) i)) =
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := by
    funext i; fin_cases i <;> simp [MvPowerSeries.map_X]
  rw [FormalGroup.map_toPowerSeries]
  conv_lhs => rw [h]
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, hswap]

end L3Aux
p2m_reactivate "P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot.L3Aux"

open L3Aux in
set_option maxHeartbeats 6400000 in
theorem L3Aux.main_aux
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) [G.IsComm] [G'.IsComm] (hG : G.IsBaseChange resT F₀)
    (hGG' : ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n G.toPowerSeries - MvPowerSeries.coeff n G'.toPowerSeries ∈ I)
    (hc : PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q))
    (Tq : Type) [CommRing Tq] [IsLocalRing Tq] (mkJ : U' I →+* Tq) (hmkJs : Function.Surjective mkJ)
    (hmkJ0 : ∀ u : U' I, mkJ u = 0 ↔ u ∈ J I hI)
    (resQ : Tq →+* k) (resPP_mk : ∀ u : U' I, resQ (mkJ u) = resT u.1.fst)
    (sec : k →+* Tq) (hsec : ∀ a : k, resQ (sec a) = a)
    (hkerQ : RingHom.ker resQ = maximalIdeal Tq) (hsqQ : ∀ a b : Tq, resQ a = 0 → resQ b = 0 → a * b = 0) :
    ∃ ψ : FormalGroup.LawIso G G', ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈ I := by
  classical
  have hII : I * I = ⊥ := le_bot_iff.mp (hI ▸ Ideal.mul_mono_right hIm)
  have hsq : maximalIdeal Tq ^ 2 = ⊥ := by
    rw [← hkerQ, pow_two, ← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    exact hsqQ a b ((RingHom.mem_ker).mp ha) ((RingHom.mem_ker).mp hb)
  letI algQ : Algebra k Tq := RingHom.toAlgebra sec
  have hresPP : ∀ a : k, resQ (algebraMap k Tq a) = a := hsec
  have hmkJeq : ∀ a b : U' I, mkJ a = mkJ b ↔ a - b ∈ J I hI := fun a b => by
    rw [← hmkJ0, map_sub, sub_eq_zero]
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]

  have hmap : MvPowerSeries.map (Ideal.Quotient.mk I) G.toPowerSeries = MvPowerSeries.map (Ideal.Quotient.mk I) G'.toPowerSeries := by
    ext n; rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, Ideal.Quotient.eq]; exact hGG' n
  obtain ⟨GP, hGP⟩ : ∃ GP : FormalGroup (FP (Ideal.Quotient.mk I)), GP = pairLaw (Ideal.Quotient.mk I) G G' hmap := ⟨_, rfl⟩
  have hGPs : GP.toPowerSeries = pairS (Ideal.Quotient.mk I) G.toPowerSeries G'.toPowerSeries hmap := by rw [hGP]; rfl
  haveI : GP.IsComm := hGP ▸ pairLaw_isComm _ G G' hmap
  have hGPbc₁ : GP.IsBaseChange (π₁ (Ideal.Quotient.mk I)) G := hGP ▸ pairLaw_bc₁ _ G G' hmap
  have hGPbc₂ : GP.IsBaseChange (π₂ (Ideal.Quotient.mk I)) G' := hGP ▸ pairLaw_bc₂ _ G G' hmap
  obtain ⟨Gh, hGh⟩ : ∃ Gh : FormalGroup (U' I), Gh = G.map (inlU I) := ⟨_, rfl⟩
  obtain ⟨Gh', hGh'⟩ : ∃ Gh' : FormalGroup (U' I), Gh' = GP.map (θU I hII) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : FormalGroup Tq, A = Gh.map mkJ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : FormalGroup Tq, B = Gh'.map mkJ := ⟨_, rfl⟩
  have hGhs : Gh.toPowerSeries = MvPowerSeries.map (inlU I) G.toPowerSeries := by rw [hGh]; rfl
  have hGh's : Gh'.toPowerSeries = MvPowerSeries.map (θU I hII) GP.toPowerSeries := by rw [hGh']; rfl
  have hAs : A.toPowerSeries = MvPowerSeries.map mkJ Gh.toPowerSeries := by rw [hA]; rfl
  have hBs : B.toPowerSeries = MvPowerSeries.map mkJ Gh'.toPowerSeries := by rw [hB]; rfl
  haveI : Gh.IsComm := hGh ▸ isComm_map G _
  haveI : Gh'.IsComm := hGh' ▸ isComm_map GP _
  haveI : A.IsComm := hA ▸ isComm_map Gh _
  haveI : B.IsComm := hB ▸ isComm_map Gh' _
  have hres_inl : (resQ).comp (mkJ.comp (inlU I)) = resT := RingHom.ext fun t => by
    simp only [RingHom.comp_apply, resPP_mk, fst_inlU]
  have hres_θ : (resQ).comp (mkJ.comp (θU I hII)) = resT.comp (π₁ (Ideal.Quotient.mk I)) := RingHom.ext fun p => by
    simp only [RingHom.comp_apply, resPP_mk, fst_θU, π₁_apply]
  have hAbc : A.IsBaseChange (resQ) F₀ := by
    show F₀.toPowerSeries = MvPowerSeries.map _ A.toPowerSeries
    rw [hAs, hGhs, ← RingHom.comp_apply (MvPowerSeries.map mkJ), ← MvPowerSeries.map_comp, ← RingHom.comp_apply (MvPowerSeries.map _),
      ← MvPowerSeries.map_comp, hres_inl]
    exact hG
  have hBbc : B.IsBaseChange (resQ) F₀ := by
    show F₀.toPowerSeries = MvPowerSeries.map _ B.toPowerSeries
    rw [hBs, hGh's, ← RingHom.comp_apply (MvPowerSeries.map mkJ), ← MvPowerSeries.map_comp, ← RingHom.comp_apply (MvPowerSeries.map _),
      ← MvPowerSeries.map_comp, hres_θ, MvPowerSeries.map_comp, RingHom.comp_apply, hGPs, map_π₁_pairS]
    exact hG

  have hcAB : PowerSeries.coeff q (A.nthSeries q) = PowerSeries.coeff q (B.nthSeries q) := by
    have e1 : A.nthSeries q = PowerSeries.map (mkJ.comp (inlU I)) (G.nthSeries q) := by
      apply FormalGroup.IsBaseChange.nthSeries_eq_map G _ A
      show A.toPowerSeries = _; rw [hAs, hGhs, MvPowerSeries.map_comp]; rfl
    have e2 : B.nthSeries q = PowerSeries.map (mkJ.comp (θU I hII)) (GP.nthSeries q) := by
      apply FormalGroup.IsBaseChange.nthSeries_eq_map GP _ B
      show B.toPowerSeries = _; rw [hBs, hGh's, MvPowerSeries.map_comp]; rfl
    have e3 : G.nthSeries q = PowerSeries.map (π₁ (Ideal.Quotient.mk I)) (GP.nthSeries q) :=
      FormalGroup.IsBaseChange.nthSeries_eq_map GP _ G hGPbc₁ q
    have e4 : G'.nthSeries q = PowerSeries.map (π₂ (Ideal.Quotient.mk I)) (GP.nthSeries q) :=
      FormalGroup.IsBaseChange.nthSeries_eq_map GP _ G' hGPbc₂ q
    have hγ : θU I hII (PowerSeries.coeff q (GP.nthSeries q)) = inlU I (PowerSeries.coeff q (G.nthSeries q)) := by
      have c1 := congrArg (PowerSeries.coeff q) e3
      have c2 := congrArg (PowerSeries.coeff q) e4
      rw [PowerSeries.coeff_map] at c1 c2
      rw [← hc] at c2
      apply U'_ext I
      · rw [fst_θU, fst_inlU, c1]; rfl
      · rw [snd_θU, snd_inlU, sub_eq_zero]
        exact (c2.symm.trans c1 : _)
    rw [e1, e2, PowerSeries.coeff_map, PowerSeries.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hγ]

  obtain ⟨ψ'', hψ''⟩ := FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot q k F₀ hF₀ Tq
    hsq (resQ) hresPP hkerQ A B hAbc hBbc hcAB

  have hu : ∀ m : ℕ, ∃ u : U' I, mkJ u = PowerSeries.coeff m ψ''.series := fun m => hmkJs _
  choose u hu using hu
  have hufst : ∀ m, resT (u m).1.fst = if m = 1 then 1 else 0 := fun m => by
    rw [← hψ'' m, ← hu m, resPP_mk]
  set δ : ℕ → T := fun m => if m = 1 then 1 else 0 with hδ
  have hδres : ∀ m, resT (δ m) = if m = 1 then 1 else 0 := fun m => by
    by_cases hm : m = 1 <;> simp [hδ, hm]
  set c : ℕ → U' I := fun m => if m = 0 then 0 else mkU I (δ m) (u m).1.snd (u m).2 with hcdef
  set Ψ : PowerSeries (U' I) := PowerSeries.mk c with hΨ
  have hc0 : c 0 = 0 := by rw [hcdef]; simp
  have hcfst : ∀ m, (c m).1.fst = δ m := fun m => by
    rw [hcdef]; by_cases hm : m = 0
    · simp only [hm, if_true, fst_zero_U, hδ]; simp
    · simp only [hm, if_false, fst_mkU]
  have hcsnd : ∀ m, m ≠ 0 → (c m).1.snd = (u m).1.snd := fun m hm => by
    rw [hcdef]; simp only [hm, if_false, snd_mkU]
  have hΨJ : PowerSeries.map mkJ Ψ = ψ''.series := by
    ext m
    rw [PowerSeries.coeff_map, hΨ, PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · rw [hm, hc0, map_zero, PowerSeries.coeff_zero_eq_constantCoeff, ψ''.constantCoeff_series]
    · rw [← hu m, hmkJeq, mem_J]
      refine ⟨?_, ?_⟩
      · rw [fst_sub_U, hcfst, hmem, map_sub, hufst, hδres, sub_self]
      · rw [snd_sub_U, hcsnd m hm, sub_self]
  have hΨfst : PowerSeries.map (fstU I) Ψ = PowerSeries.X := by
    ext m
    rw [PowerSeries.coeff_map, hΨ, PowerSeries.coeff_mk, fstU_apply, hcfst, PowerSeries.coeff_X, hδ]
  have hΨ0 : PowerSeries.constantCoeff Ψ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hΨ, PowerSeries.coeff_mk, hc0]
  have hΨs : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero' hΨ0

  have hGhF : MvPowerSeries.map (fstU I) Gh.toPowerSeries = G.toPowerSeries := by
    rw [hGhs, ← RingHom.comp_apply (MvPowerSeries.map _), ← MvPowerSeries.map_comp, fstU_comp_inlU,
      MvPowerSeries.map_id, RingHom.id_apply]
  have hGh'F : MvPowerSeries.map (fstU I) Gh'.toPowerSeries = G.toPowerSeries := by
    rw [hGh's, ← RingHom.comp_apply (MvPowerSeries.map _), ← MvPowerSeries.map_comp, fstU_comp_θU, hGPs]
    exact map_π₁_pairS _ _ _ hmap
  have hcomm : PowerSeries.subst Gh.toPowerSeries Ψ =
      MvPowerSeries.subst ![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] Gh'.toPowerSeries := by
    have hGhS : PowerSeries.HasSubst Gh.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero Gh.zero_constantCoeff
    have hfam : MvPowerSeries.HasSubst (![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] : Fin 2 → MvPowerSeries (Fin 2) (U' I)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        fin_cases i <;> exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) Ψ hΨ0)

    have hF : MvPowerSeries.map (fstU I) (PowerSeries.subst Gh.toPowerSeries Ψ)
        = MvPowerSeries.map (fstU I) (MvPowerSeries.subst ![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] Gh'.toPowerSeries) := by
      rw [PowerSeries.map_subst hGhS, hGhF, hΨfst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff),
        MvPowerSeries.map_subst hfam, hGh'F]
      have : (fun i => MvPowerSeries.map (fstU I) ((![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] : Fin 2 → MvPowerSeries (Fin 2) (U' I)) i))
          = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) T), MvPowerSeries.X 1] := by
        funext i; fin_cases i <;>
        · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, LawHom.substX]
          rw [PowerSeries.map_subst (PowerSeries.HasSubst.X _), MvPowerSeries.map_X, hΨfst, PowerSeries.subst_X (PowerSeries.HasSubst.X _)]
      rw [this, MvPowerSeries.subst_X_pair_eq_self]

    have hM : MvPowerSeries.map mkJ (PowerSeries.subst Gh.toPowerSeries Ψ)
        = MvPowerSeries.map mkJ (MvPowerSeries.subst ![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] Gh'.toPowerSeries) := by
      rw [PowerSeries.map_subst hGhS, hΨJ, MvPowerSeries.map_subst hfam]
      have e1 : MvPowerSeries.map mkJ Gh.toPowerSeries = A.toPowerSeries := hAs.symm
      have e2 : MvPowerSeries.map mkJ Gh'.toPowerSeries = B.toPowerSeries := hBs.symm
      have e3 : (fun i => MvPowerSeries.map mkJ ((![LawHom.substX 0 Ψ, LawHom.substX 1 Ψ] : Fin 2 → MvPowerSeries (Fin 2) (U' I)) i))
          = ![LawHom.substX 0 ψ''.series, LawHom.substX 1 ψ''.series] := by
        funext i; fin_cases i <;>
        · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, LawHom.substX]
          rw [PowerSeries.map_subst (PowerSeries.HasSubst.X _), MvPowerSeries.map_X, hΨJ]
      rw [e1, e2, e3]
      exact ψ''.comm

    refine MvPowerSeries.ext fun d => ?_
    have h1 := congrArg (MvPowerSeries.coeff d) hF
    have h2 := congrArg (MvPowerSeries.coeff d) hM
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, fstU_apply] at h1
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, hmkJeq, mem_J, fst_sub_U, snd_sub_U] at h2
    apply U'_ext I
    · exact h1
    · exact sub_eq_zero.mp h2.2
  let Ψhom : FormalGroup.LawHom Gh Gh' := ⟨Ψ, hΨ0, hcomm⟩

  have hbcG : Gh.IsBaseChange (σU I hII) G := by
    show G.toPowerSeries = MvPowerSeries.map (σU I hII) Gh.toPowerSeries
    rw [hGhs, ← RingHom.comp_apply (MvPowerSeries.map _), ← MvPowerSeries.map_comp, σU_comp_inlU,
      MvPowerSeries.map_id, RingHom.id_apply]
  have hbcG' : Gh'.IsBaseChange (σU I hII) G' := by
    show G'.toPowerSeries = MvPowerSeries.map (σU I hII) Gh'.toPowerSeries
    rw [hGh's, ← RingHom.comp_apply (MvPowerSeries.map _), ← MvPowerSeries.map_comp, σU_comp_θU, hGPs]
    exact (map_π₂_pairS _ _ _ hmap).symm
  obtain ⟨θ, hθ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map (σU I hII) Ψhom G G' hbcG hbcG'
  have hθc : ∀ m, PowerSeries.coeff m θ.series = δ m + (c m).1.snd := fun m => by
    rw [hθ, PowerSeries.coeff_map, show Ψhom.series = Ψ from rfl, hΨ, PowerSeries.coeff_mk, σU_apply, hcfst]
  have hunit : IsUnit (PowerSeries.coeff 1 θ.series) := by
    rw [hθc, hcsnd 1 one_ne_zero, hδ]
    simp only [if_true]
    have hm : -(u 1).1.snd ∈ maximalIdeal T := hIm (I.neg_mem (u 1).2)
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(u 1).1.snd) hm
    rwa [sub_neg_eq_add] at this
  refine ⟨⟨θ, hunit⟩, fun m => ?_⟩
  show PowerSeries.coeff m θ.series - (if m = 1 then 1 else 0) ∈ I
  rw [hθc, hδ]
  simp only [add_sub_cancel_left]
  by_cases hm : m = 0
  · rw [hm, hc0]; simp
  · rw [hcsnd m hm]; exact (u m).2

open L3Aux in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) [G.IsComm] [G'.IsComm] (hG : G.IsBaseChange resT F₀)
    (hGG' : ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n G.toPowerSeries - MvPowerSeries.coeff n G'.toPowerSeries ∈ I)
    (hc : PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q)) :
    ∃ ψ : FormalGroup.LawIso G G', ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈ I := by
  exact L3Aux.main_aux q k F₀ hF₀ T I hI hIm resT hresT hkerT G G' hG hGG' hc (U' I ⧸ J I hI)
    (Ideal.Quotient.mk (J I hI)) Ideal.Quotient.mk_surjective (fun u => Ideal.Quotient.eq_zero_iff_mem)
    (resPP I hI resT hkerT) (resPP_mk I hI resT hkerT) (secPP I hI resT hresT hkerT) (resPP_secPP I hI resT hresT hkerT)
    (ker_resPP I hI resT hresT hkerT) (resPP_mul_eq_zero I hI resT hresT hkerT)

end S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot (solution)
