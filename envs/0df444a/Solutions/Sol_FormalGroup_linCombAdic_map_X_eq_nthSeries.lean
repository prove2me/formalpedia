-- Prove2me | solution 1 for FormalGroup.linCombAdic_map_X_eq_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/29708dd6-6199-59df-86e1-febac9637c30

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_FormalGroup_evalSeries_nthSeries
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_evalSeries_map_algebraMap_eq_subst
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_linCombAdic_map_X_eq_nthSeries

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DW2N1D

open MvPowerSeries Filter Topology

theorem subst_pair_zero_right {T : Type*} [CommRing T] (F : FormalGroup T) {τ : Type*}
    (A : MvPowerSeries τ T) (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.subst ![A, 0] F.toPowerSeries = A := by
  have hfam : MvPowerSeries.HasSubst
      (Sum.elim (fun _ : Fin 1 => A) (fun _ : Fin 1 => (0 : MvPowerSeries τ T))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by rcases s with _ | _ <;> simp [hA])
  have h := MvFormalGroup.subst_elim_zero_right (MvFormalGroup.ofFormalGroup F)
    (a := fun _ : Fin 1 => A) (fun _ => hA) 0
  rw [show (MvFormalGroup.ofFormalGroup F).toPowerSeries 0 =
        MvPowerSeries.rename MvFormalGroup.e2 F.toPowerSeries from rfl,
    MvFormalGroup.subst_rename _ hfam] at h
  have hv : (fun s : Fin 2 => Sum.elim (fun _ : Fin 1 => A) (fun _ : Fin 1 => (0 : MvPowerSeries τ T))
      (MvFormalGroup.e2 s)) = ![A, 0] := by
    funext s; fin_cases s <;> simp
  rw [hv] at h
  exact h

theorem subst_pair_zero_left {T : Type*} [CommRing T] (F : FormalGroup T) {τ : Type*}
    (A : MvPowerSeries τ T) (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.subst ![0, A] F.toPowerSeries = A := by
  have hfam : MvPowerSeries.HasSubst
      (Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries τ T)) (fun _ : Fin 1 => A)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by rcases s with _ | _ <;> simp [hA])
  have h := MvFormalGroup.subst_elim_zero_left (MvFormalGroup.ofFormalGroup F)
    (a := fun _ : Fin 1 => A) (fun _ => hA) 0
  rw [show (MvFormalGroup.ofFormalGroup F).toPowerSeries 0 =
        MvPowerSeries.rename MvFormalGroup.e2 F.toPowerSeries from rfl,
    MvFormalGroup.subst_rename _ hfam] at h
  have hv : (fun s : Fin 2 => Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries τ T)) (fun _ : Fin 1 => A)
      (MvFormalGroup.e2 s)) = ![0, A] := by
    funext s; fin_cases s <;> simp
  rw [hv] at h
  exact h

section Values

variable {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
  {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A]

theorem hasEval_of_mem {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) :
    letI : WithIdeal A := ⟨I⟩; MvPowerSeries.HasEval a := by
  letI : WithIdeal A := ⟨I⟩
  refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), ?_⟩
  rw [Filter.cofinite_eq_bot]; exact tendsto_bot

theorem eval₂_mem {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) (f : MvPowerSeries σ R₀)
    (hf : algebraMap R₀ A (MvPowerSeries.constantCoeff f) ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) a f) ∈ I := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I a ha) f
  have hopen : IsOpen ((Submodule.toAddSubgroup I : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨1, trivial, by simp⟩
  have hclosed : IsClosed (I : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  refine hclosed.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  refine I.sum_mem fun d _ => ?_
  by_cases hd : d = 0
  · subst hd; simpa using hf
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    refine I.mul_mem_left _ ?_
    rw [Finsupp.prod]
    exact I.prod_mem hi (I.pow_mem_of_mem (ha i) _ (Nat.pos_of_ne_zero hi'))

theorem eval₂_comm (F : FormalGroup R₀) [hF : F.IsComm] (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![x, y] F.toPowerSeries) =
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![y, x] F.toPowerSeries) := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hb : MvPowerSeries.HasEval (![y, x] : Fin 2 → A) :=
    hasEval_of_mem I _ (fun s => by fin_cases s <;> simp [hx, hy])
  have key := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A) MvPowerSeries.HasSubst.X_X hb F.toPowerSeries
    (a := ![MvPowerSeries.X 1, MvPowerSeries.X 0])
  rw [← hF.comm] at key
  rw [key]
  congr 1
  funext s; fin_cases s <;> simp [MvPowerSeries.eval₂_X]

theorem eval₂_assoc (F : FormalGroup R₀) (x y z : A) (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A)
      ![MvPowerSeries.eval₂ (algebraMap R₀ A) ![x, y] F.toPowerSeries, z] F.toPowerSeries) =
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A)
      ![x, MvPowerSeries.eval₂ (algebraMap R₀ A) ![y, z] F.toPowerSeries] F.toPowerSeries) := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hc : MvPowerSeries.HasEval (![x, y, z] : Fin 3 → A) :=
    hasEval_of_mem I _ (fun s => by fin_cases s <;> simp [hx, hy, hz])
  have h0 := F.zero_constantCoeff
  have eL := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A)
    (MvPowerSeries.HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 h0) hc F.toPowerSeries
  have eR := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A)
    (MvPowerSeries.HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 h0) hc F.toPowerSeries
  have eXY := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A)
    (MvPowerSeries.HasSubst.X_X (i := (0 : Fin 3)) (j := 1)) hc F.toPowerSeries
  have eYZ := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A)
    (MvPowerSeries.HasSubst.X_X (i := (1 : Fin 3)) (j := 2)) hc F.toPowerSeries
  have hassoc := congrArg (MvPowerSeries.eval₂ (algebraMap R₀ A) (![x, y, z] : Fin 3 → A)) F.assoc
  rw [eL, eR] at hassoc
  have hxy : (fun s : Fin 2 => MvPowerSeries.eval₂ (algebraMap R₀ A) (![x, y, z] : Fin 3 → A)
      ((![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) R₀) s)) = ![x, y] := by
    funext s; fin_cases s <;> simp [MvPowerSeries.eval₂_X]
  have hyz : (fun s : Fin 2 => MvPowerSeries.eval₂ (algebraMap R₀ A) (![x, y, z] : Fin 3 → A)
      ((![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R₀) s)) = ![y, z] := by
    funext s; fin_cases s <;> simp [MvPowerSeries.eval₂_X]
  rw [hxy] at eXY
  rw [hyz] at eYZ
  convert hassoc using 2
  · funext s; fin_cases s
    · simpa using eXY.symm
    · simp [MvPowerSeries.eval₂_X]
  · funext s; fin_cases s
    · simp [MvPowerSeries.eval₂_X]
    · simpa using eYZ.symm

theorem eval₂_pair_zero (F : FormalGroup R₀) (x : A) (hx : x ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![x, 0] F.toPowerSeries) = x ∧
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![0, x] F.toPowerSeries) = x := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hb : MvPowerSeries.HasEval (fun _ : Unit => x) := by
    refine ⟨fun _ => WithIdeal.isTopologicallyNilpotent_of_mem hx, ?_⟩
    rw [Filter.cofinite_eq_bot]; exact tendsto_bot
  have hbX : MvPowerSeries.eval₂ (algebraMap R₀ A) (fun _ : Unit => x) (PowerSeries.X : PowerSeries R₀) = x :=
    MvPowerSeries.eval₂_X _ _ ()
  have hb0 : MvPowerSeries.eval₂ (algebraMap R₀ A) (fun _ : Unit => x) (0 : PowerSeries R₀) = 0 := by
    rw [show (0 : PowerSeries R₀) = MvPowerSeries.C (0 : R₀) from (map_zero _).symm, MvPowerSeries.eval₂_C, map_zero]
  have hX0 : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R₀) = 0 := MvPowerSeries.constantCoeff_X _
  constructor
  · have ha : MvPowerSeries.HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries R₀) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
        fin_cases s
        · exact hX0
        · exact map_zero _)
    have key := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A) ha hb F.toPowerSeries
    rw [subst_pair_zero_right F (PowerSeries.X : PowerSeries R₀) hX0, hbX] at key
    refine Eq.trans ?_ key.symm
    congr 1
    funext s; fin_cases s
    · simpa using hbX.symm
    · simpa using hb0.symm
  · have ha : MvPowerSeries.HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R₀) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
        fin_cases s
        · exact map_zero _
        · exact hX0)
    have key := MvPowerSeries.eval₂_subst (R := R₀) (S := R₀) (T := A) ha hb F.toPowerSeries
    rw [subst_pair_zero_left F (PowerSeries.X : PowerSeries R₀) hX0, hbX] at key
    refine Eq.trans ?_ key.symm
    congr 1
    funext s; fin_cases s
    · simpa using hb0.symm
    · simpa using hbX.symm

theorem eval₂_sub_add_mem_sq (F : FormalGroup R₀) (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![x, y] F.toPowerSeries) - (x + y) ∈ I ^ 2 := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have ha : ∀ s, (![x, y] : Fin 2 → A) s ∈ I := fun s => by fin_cases s <;> simp [hx, hy]
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I (![x, y] : Fin 2 → A) ha) F.toPowerSeries
  have hopen : IsOpen ((Submodule.toAddSubgroup (I ^ 2) : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨2, trivial, by simp⟩
  have hclosed : IsClosed ((I ^ 2 : Ideal A) : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  have hclosed' : IsClosed {z : A | z - (x + y) ∈ I ^ 2} :=
    hclosed.preimage (continuous_id.sub continuous_const)
  refine hclosed'.mem_of_tendsto hsum (Filter.eventually_atTop.mpr ⟨{Finsupp.single 0 1, Finsupp.single 1 1}, ?_⟩)
  intro s hs
  have h01 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h; have := congrArg (fun e => e 0) h; simp at this
  have hmem0 : Finsupp.single (0 : Fin 2) 1 ∈ s := hs (by simp)
  have hmem1 : Finsupp.single (1 : Fin 2) 1 ∈ s := hs (by simp)
  show (∑ d ∈ s, _) - (x + y) ∈ I ^ 2
  rw [← Finset.add_sum_erase s _ hmem0, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, hmem1⟩)]
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = x ^ (d 0) * y ^ (d 1) := by
    intro d; rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]; rfl
  have t0 : algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F.toPowerSeries) *
      ((Finsupp.single (0 : Fin 2) 1).prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = x := by
    rw [F.lin_coeff_X, map_one, one_mul, hprod]; simp
  have t1 : algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F.toPowerSeries) *
      ((Finsupp.single (1 : Fin 2) 1).prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = y := by
    rw [F.lin_coeff_Y, map_one, one_mul, hprod]; simp
  rw [t0, t1, show ∀ S : A, x + (y + S) - (x + y) = S from fun S => by ring]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [Finset.mem_erase, Finset.mem_erase] at hd
  obtain ⟨hd1, hd0, -⟩ := hd
  by_cases hz : d = 0
  · subst hz; rw [MvPowerSeries.coeff_zero_eq_constantCoeff, F.zero_constantCoeff, map_zero, zero_mul]; exact Submodule.zero_mem _
  refine Ideal.mul_mem_left _ _ ?_
  rw [hprod]
  have hdeg : 2 ≤ d 0 + d 1 := by
    by_contra hlt
    push_neg at hlt
    have h0 : d 0 ≤ 1 := by omega
    have h1 : d 1 ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with e0 | e0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with e1 | e1
    · exact hz (by ext i; fin_cases i <;> simp [e0, e1])
    · exact hd1 (by ext i; fin_cases i <;> simp [e0, e1])
    · exact hd0 (by ext i; fin_cases i <;> simp [e0, e1])
    · omega
  have hxy : x ^ d 0 * y ^ d 1 ∈ I ^ (d 0 + d 1) := by
    rw [pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)
  exact Ideal.pow_le_pow_right hdeg hxy

end Values

end DW2N1D

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) (w : PowerSeries T) (hw : w ∈ maximalIdeal (PowerSeries T)) :
    (F.map (algebraMap T (PowerSeries T))).linCombAdic (maximalIdeal (PowerSeries T)) PowerSeries.X w q 0 =
      F.nthSeries q := by
  classical
  letI Wd : WithIdeal (PowerSeries T) := ⟨maximalIdeal (PowerSeries T)⟩
  haveI hcomp : IsAdicComplete (maximalIdeal (PowerSeries T)) (PowerSeries T) := MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := T)
  have hI : IsAdic (maximalIdeal (PowerSeries T)) := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp hcomp
  haveI := hcs
  haveI := ht2
  set 𝔪 := maximalIdeal (PowerSeries T) with h𝔪
  set F' : FormalGroup (PowerSeries T) := F.map (algebraMap T (PowerSeries T)) with hF'
  have hXm : (PowerSeries.X : PowerSeries T) ∈ 𝔪 := by
    rw [h𝔪, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero

  have hmem : ∀ x y : PowerSeries T, x ∈ 𝔪 → y ∈ 𝔪 → F'.eval x y ∈ 𝔪 := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2N1D.eval₂_mem (PowerSeries T) _ ⊥ inferInstance (PowerSeries T) _ _ 𝔪 hcomp (Fin 2) _ ![x, y]
      (fun s => by fin_cases s <;> simp [hx, hy]) F'.toPowerSeries
      (by rw [F'.zero_constantCoeff, map_zero]; exact Submodule.zero_mem _)
  have hzero : ∀ x : PowerSeries T, x ∈ 𝔪 → F'.eval x 0 = x := by
    intro x hx
    unfold FormalGroup.eval
    exact (@DW2N1D.eval₂_pair_zero (PowerSeries T) _ ⊥ inferInstance (PowerSeries T) _ _ 𝔪 hcomp F' x hx).1
  have hNmem : ∀ (n : ℕ) (x : PowerSeries T), x ∈ 𝔪 → F'.evalNSMul n x ∈ 𝔪 := by
    intro n x hx
    induction n with
    | zero => exact Submodule.zero_mem _
    | succ n ih => rw [FormalGroup.evalNSMul_succ]; exact hmem _ _ ih hx

  show F'.eval (F'.evalNSMul q PowerSeries.X) (F'.evalNSMul 0 w) = F.nthSeries q
  rw [FormalGroup.evalNSMul_zero, hzero _ (hNmem q _ hXm)]

  rw [← FormalGroup.evalSeries_nthSeries F' (WithIdeal.isTopologicallyNilpotent_of_mem hXm) q]

  have hbc : F.IsBaseChange (algebraMap T (PowerSeries T)) F' := by
    show F'.toPowerSeries = MvPowerSeries.map (algebraMap T (PowerSeries T)) F.toPowerSeries; rw [hF']; rfl
  rw [FormalGroup.IsBaseChange.nthSeries_eq_map F (algebraMap T (PowerSeries T)) F' hbc q,
    FormalGroup.evalSeries_map_algebraMap_eq_subst (F.nthSeries q) PowerSeries.X (PowerSeries.constantCoeff_X)]

  ext m
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_X (R := T))), finsum_eq_single _ m (fun n hn => by
    rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hn), smul_zero]), PowerSeries.coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one]

end S_FormalGroup_linCombAdic_map_X_eq_nthSeries
end P2MW
export P2MW.S_FormalGroup_linCombAdic_map_X_eq_nthSeries (solution)
