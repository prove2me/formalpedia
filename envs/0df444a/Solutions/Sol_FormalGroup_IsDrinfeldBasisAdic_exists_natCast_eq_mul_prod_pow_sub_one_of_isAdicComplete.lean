-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/084d390d-d198-553c-af58-ad2d6e96e9ee

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Theorems.Thm_FormalGroup_evalSeries_nthSeries
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_smul_add_sq_mul
import Theorems.Thm_FormalGroup_coeff_one_nthSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing FormalGroup

namespace DW2HP

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

end DW2HP

set_option maxHeartbeats 8000000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (F : FormalGroup R) [F.IsComm] (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁) :
    ∃ (u : R) (_ : IsUnit u) (P : ZMod q → R),
      (∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ maximalIdeal R ^ 2) ∧
      ((q : ℕ) : R) = u * (x₀ * ∏ c : ZMod q, P c) ^ (q - 1) := by
  classical
  letI W : WithIdeal R := ⟨maximalIdeal R⟩
  have HI : IsAdic (maximalIdeal R) := rfl
  obtain ⟨hcs, ht2⟩ := HI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal R) R)
  haveI := hcs
  haveI := ht2
  set 𝔪 := maximalIdeal R with h𝔪
  have hqp : q.Prime := Fact.out
  have hq1 : 1 ≤ q := hqp.one_lt.le
  have hq2 : 2 ≤ q := hqp.two_le
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  have hmem : ∀ x y : R, x ∈ 𝔪 → y ∈ 𝔪 → F.eval x y ∈ 𝔪 := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2HP.eval₂_mem R _ ⊥ inferInstance R _ _ 𝔪 _ (Fin 2) _ ![x, y]
      (fun s => by fin_cases s <;> simp [hx, hy]) F.toPowerSeries
      (by rw [F.zero_constantCoeff, map_zero]; exact Submodule.zero_mem _)
  have hlin : ∀ x y : R, x ∈ 𝔪 → y ∈ 𝔪 → F.eval x y - (x + y) ∈ 𝔪 ^ 2 := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2HP.eval₂_sub_add_mem_sq R _ ⊥ inferInstance R _ _ 𝔪 _ F x y hx hy
  have hcomm : ∀ x y : R, x ∈ 𝔪 → y ∈ 𝔪 → F.eval x y = F.eval y x := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2HP.eval₂_comm R _ ⊥ inferInstance R _ _ 𝔪 _ F _ x y hx hy
  have hassoc : ∀ x y z : R, x ∈ 𝔪 → y ∈ 𝔪 → z ∈ 𝔪 →
      F.eval (F.eval x y) z = F.eval x (F.eval y z) := by
    intro x y z hx hy hz
    unfold FormalGroup.eval
    exact @DW2HP.eval₂_assoc R _ ⊥ inferInstance R _ _ 𝔪 _ F x y z hx hy hz
  have hzero : ∀ x : R, x ∈ 𝔪 → F.eval x 0 = x ∧ F.eval 0 x = x := by
    intro x hx
    unfold FormalGroup.eval
    exact @DW2HP.eval₂_pair_zero R _ ⊥ inferInstance R _ _ 𝔪 _ F x hx
  have hNmem : ∀ (n : ℕ) (x : R), x ∈ 𝔪 → F.evalNSMul n x ∈ 𝔪 := by
    intro n x hx
    induction n with
    | zero => exact Submodule.zero_mem _
    | succ n ih => rw [FormalGroup.evalNSMul_succ]; exact hmem _ _ ih hx
  have hN0 : ∀ n : ℕ, F.evalNSMul n (0 : R) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [FormalGroup.evalNSMul_succ, ih]; exact (hzero 0 (Submodule.zero_mem _)).1
  have hN1 : ∀ x : R, x ∈ 𝔪 → F.evalNSMul 1 x = x := by
    intro x hx; rw [FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_zero]; exact (hzero x hx).2
  have hNadd : ∀ (n : ℕ) (x y : R), x ∈ 𝔪 → y ∈ 𝔪 →
      F.evalNSMul n (F.eval x y) = F.eval (F.evalNSMul n x) (F.evalNSMul n y) := by
    intro n x y hx hy
    induction n with
    | zero => simp only [FormalGroup.evalNSMul_zero]; exact (hzero 0 (Submodule.zero_mem _)).1.symm
    | succ n ih =>
      rw [FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, ih]
      have h1 := hNmem n x hx
      have h2 := hNmem n y hy
      rw [hassoc _ _ _ h1 h2 (hmem _ _ hx hy), ← hassoc _ _ _ h2 hx hy, hcomm _ _ h2 hx,
        hassoc _ _ _ hx h2 hy, ← hassoc _ _ _ h1 hx (hmem _ _ h2 hy)]
  have hNaddExp : ∀ (m n : ℕ) (x : R), x ∈ 𝔪 →
      F.evalNSMul (m + n) x = F.eval (F.evalNSMul m x) (F.evalNSMul n x) := by
    intro m n x hx
    induction n with
    | zero => rw [_root_.add_zero, FormalGroup.evalNSMul_zero]; exact (hzero _ (hNmem m x hx)).1.symm
    | succ n ih =>
      rw [← add_assoc, FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, ih,
        hassoc _ _ _ (hNmem m x hx) (hNmem n x hx) hx]
  have hNmul : ∀ (m n : ℕ) (x : R), x ∈ 𝔪 → F.evalNSMul n (F.evalNSMul m x) = F.evalNSMul (m * n) x := by
    intro m n x hx
    induction n with
    | zero => rfl
    | succ n ih => rw [FormalGroup.evalNSMul_succ, ih, Nat.mul_succ, hNaddExp _ _ _ hx]

  have heval : ∀ z : R, z ∈ 𝔪 → ∃ e : PowerSeries R →+* R, (∀ n, F.evalNSMul n z = e (F.nthSeries n)) ∧
      e PowerSeries.X = z ∧ ∀ c : R, e (PowerSeries.C c) = c := by
    intro z hz
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal R) z hz
    refine ⟨e, fun n => ?_, ?_, fun c => ?_⟩
    · rw [← he, FormalGroup.evalSeries_nthSeries F (WithIdeal.isTopologicallyNilpotent_of_mem hz) n]
    · have := hep Polynomial.X; rwa [Polynomial.coe_X, Polynomial.eval_X] at this
    · have := hep (Polynomial.C c); rwa [Polynomial.coe_C, Polynomial.eval_C] at this
  have hNlin : ∀ (n : ℕ) (z : R), z ∈ 𝔪 → ∃ w : R, w - (n : R) ∈ 𝔪 ∧ F.evalNSMul n z = z * w := by
    intro n z hz
    obtain ⟨e, he, heX, heC⟩ := heval z hz
    obtain ⟨Gn, hGn⟩ := F.exists_nthSeries_eq_smul_add_sq_mul n
    refine ⟨(n : R) + z * e Gn, ?_, ?_⟩
    · rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ hz
    · rw [he n, hGn, map_add, map_mul, map_pow, PowerSeries.smul_eq_C_mul, map_mul, heC, heX]; ring

  obtain ⟨U, hU, hqU⟩ := (FormalGroup.isDrinfeldBasisAdic_iff F (maximalIdeal R) q x₀ x₁).mp hD
  set ℓ : ℕ → ℕ → R := fun a b => F.linComb x₀ x₁ a b with hℓ
  have hℓdef : ∀ a b, ℓ a b = F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁) := fun a b => rfl
  have hℓmem : ∀ a b, ℓ a b ∈ 𝔪 := fun a b => by rw [hℓdef]; exact hmem _ _ (hNmem a _ hx₀) (hNmem b _ hx₁)
  have hℓ00 : ℓ 0 0 = 0 := by rw [hℓdef]; simp only [FormalGroup.evalNSMul_zero]; exact (hzero 0 (Submodule.zero_mem _)).1
  have hℓ10 : ℓ 1 0 = x₀ := by rw [hℓdef, hN1 x₀ hx₀, FormalGroup.evalNSMul_zero]; exact (hzero x₀ hx₀).1
  have hℓ01 : ℓ 0 1 = x₁ := by rw [hℓdef, hN1 x₁ hx₁, FormalGroup.evalNSMul_zero]; exact (hzero x₁ hx₁).2
  have hDiv : F.drinfeldDivisorAdic (maximalIdeal R) q x₀ x₁ =
      ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (ℓ a b)) := rfl
  rw [hDiv] at hqU

  have hkill : ∀ z : R, z ∈ 𝔪 → (∃ a ∈ Finset.range q, ∃ b ∈ Finset.range q, ℓ a b = z) → F.evalNSMul q z = 0 := by
    intro z hz ⟨a, ha, b, hb, hab⟩
    obtain ⟨e, he, heX, heC⟩ := heval z hz
    rw [he q, hqU, map_mul, map_prod]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero ha
    rw [map_prod]; apply Finset.prod_eq_zero hb
    rw [map_sub, heX, heC, hab, sub_self]
  have hq0 : 0 < q := hq1
  have hqx₀ : F.evalNSMul q x₀ = 0 := hkill x₀ hx₀ ⟨1, Finset.mem_range.mpr hqp.one_lt, 0, Finset.mem_range.mpr hq0, hℓ10⟩
  have hqx₁ : F.evalNSMul q x₁ = 0 := hkill x₁ hx₁ ⟨0, Finset.mem_range.mpr hq0, 1, Finset.mem_range.mpr hqp.one_lt, hℓ01⟩
  have hper : ∀ (x : R), x ∈ 𝔪 → F.evalNSMul q x = 0 → ∀ n : ℕ, F.evalNSMul n x = F.evalNSMul (n % q) x := by
    intro x hx hqx n
    conv_lhs => rw [← Nat.mod_add_div n q, hNaddExp _ _ _ hx, ← hNmul _ _ _ hx, hqx, hN0]
    exact (hzero _ (hNmem _ _ hx)).1

  have hscale : ∀ t a b : ℕ, ℓ ((t * a) % q) ((t * b) % q) = F.evalNSMul t (ℓ a b) := by
    intro t a b
    rw [hℓdef, hℓdef, ← hper x₀ hx₀ hqx₀, ← hper x₁ hx₁ hqx₁, mul_comm t a, mul_comm t b, ← hNmul _ _ _ hx₀, ← hNmul _ _ _ hx₁,
      hNadd _ _ _ (hNmem _ _ hx₀) (hNmem _ _ hx₁)]

  have conv1 : ∀ g : ℕ → PowerSeries R, ∏ a ∈ Finset.range q, g a = ∏ z : ZMod q, g z.val := by
    intro g
    refine (Finset.prod_nbij (fun z : ZMod q => z.val) (fun z _ => Finset.mem_range.mpr (ZMod.val_lt z))
      (fun z _ z' _ h => ZMod.val_injective q h) (fun a ha => ?_) (fun z _ => rfl)).symm
    refine ⟨(a : ZMod q), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  set L : ZMod q × ZMod q → R := fun p => ℓ p.1.val p.2.val with hL
  have hDZ : (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (ℓ a b)))
      = ∏ p : ZMod q × ZMod q, (PowerSeries.X - PowerSeries.C (L p)) := by
    rw [conv1]
    simp_rw [conv1]
    rw [← Fintype.prod_prod_type']
  have hL0 : L 0 = 0 := by rw [hL]; simp only [Prod.fst_zero, Prod.snd_zero, ZMod.val_zero]; exact hℓ00
  set S : Finset (ZMod q × ZMod q) := Finset.univ.erase 0 with hS
  have hprodS : (∏ p : ZMod q × ZMod q, (PowerSeries.X - PowerSeries.C (L p)))
      = PowerSeries.X * ∏ p ∈ S, (PowerSeries.X - PowerSeries.C (L p)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod q × ZMod q)), hL0, map_zero, sub_zero]

  have hcoef : ((q : ℕ) : R) = PowerSeries.constantCoeff U * ∏ p ∈ S, (-(L p)) := by
    have h := congrArg (PowerSeries.coeff 1) hqU
    rw [FormalGroup.coeff_one_nthSeries, hDZ, hprodS, ← mul_assoc, mul_comm U, mul_assoc] at h
    have e2 : PowerSeries.coeff 1 (PowerSeries.X * (U * ∏ p ∈ S, (PowerSeries.X - PowerSeries.C (L p))))
        = PowerSeries.constantCoeff U * ∏ p ∈ S, (-(L p)) := by
      rw [show (PowerSeries.coeff (R := R) 1) = PowerSeries.coeff (0 + 1) from rfl, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub]
    rw [e2] at h
    exact h

  have hLmem : ∀ p, L p ∈ 𝔪 := fun p => hℓmem _ _
  have hqm : ((q : ℕ) : R) ∈ 𝔪 := by
    rw [hcoef]
    have h10 : ((1 : ZMod q), (0 : ZMod q)) ∈ S := by
      rw [hS, Finset.mem_erase]; exact ⟨by simp, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => -(L p)) h10
    rw [hc, ← mul_assoc, mul_comm _ (-(L (1, 0))), mul_assoc]
    exact Ideal.mul_mem_right _ _ (𝔪.neg_mem (hLmem _))
  have hunitNat : ∀ t : ℕ, 0 < t → t < q → IsUnit ((t : ℕ) : R) := by
    intro t ht0 htq
    by_contra hu
    have htm : ((t : ℕ) : R) ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have hcop : Nat.Coprime t q := (Nat.coprime_comm.mp (hqp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht0 htq)))
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
    have h1 : (1 : R) ∈ 𝔪 := by
      have := congrArg (Int.cast : ℤ → R) huv
      push_cast at this
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hqm)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top (h𝔪 ▸ h1)

  have hW : ∀ (t : ℕ) (z : R), 0 < t → t < q → z ∈ 𝔪 → ∃ w : R, IsUnit w ∧ F.evalNSMul t z = z * w := by
    intro t z ht0 htq hz
    obtain ⟨w, hw, he⟩ := hNlin t z hz
    refine ⟨w, ?_, he⟩
    by_contra hu
    have hwm : w ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have : ((t : ℕ) : R) ∈ 𝔪 := by
      have := 𝔪.sub_mem hwm hw; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp (h𝔪 ▸ this) (hunitNat t ht0 htq)
  choose wfun hwunit hweq using fun (p : {t : ℕ // 0 < t ∧ t < q} × {z : R // z ∈ 𝔪}) =>
    hW p.1.1 p.2.1 p.1.2.1 p.1.2.2 p.2.2

  set P : ZMod q → R := fun c => ℓ c.val 1 with hP
  have hPmem : ∀ c, P c ∈ 𝔪 := fun c => hℓmem _ _
  have hPlin : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2 := by
    intro c
    obtain ⟨w, hw, he⟩ := hNlin c.val x₀ hx₀
    have h1 := hlin (F.evalNSMul c.val x₀) x₁ (hNmem _ _ hx₀) hx₁
    have h2 : F.evalNSMul c.val x₀ - ((c.val : ℕ) : R) * x₀ ∈ 𝔪 ^ 2 := by
      rw [he, show x₀ * w - ((c.val : ℕ) : R) * x₀ = x₀ * (w - (c.val : ℕ)) by ring, pow_two]
      exact Ideal.mul_mem_mul hx₀ hw
    have : P c - (x₁ + ((c.val : ℕ) : R) * x₀)
        = (F.eval (F.evalNSMul c.val x₀) x₁ - (F.evalNSMul c.val x₀ + x₁)) + (F.evalNSMul c.val x₀ - ((c.val : ℕ) : R) * x₀) := by
      show ℓ c.val 1 - _ = _
      rw [hℓdef, hN1 x₁ hx₁]; ring
    rw [this]
    exact Ideal.add_mem _ h1 h2

  have hUprod : ∀ (s : Finset (ZMod q)) (f : ZMod q → R), (∀ i ∈ s, IsUnit (f i)) → IsUnit (∏ i ∈ s, f i) :=
    fun s f hf => Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one hf
  have hval : ∀ β : ZMod q, β ≠ 0 → 0 < β.val ∧ β.val < q := fun β hβ =>
    ⟨Nat.pos_of_ne_zero (fun h => hβ ((ZMod.val_eq_zero β).mp h)), ZMod.val_lt β⟩

  set g : ZMod q × ZMod q → R := fun p => if p = 0 then 1 else L p with hg
  have hSg : ∏ p ∈ S, L p = ∏ p : ZMod q × ZMod q, g p := by
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ (0 : ZMod q × ZMod q))]
    rw [show g 0 = 1 from if_pos rfl, one_mul, hS]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hg]; beta_reduce; rw [if_neg (Finset.ne_of_mem_erase hp)]
  have hsplit : ∏ p ∈ S, L p = (∏ α ∈ (Finset.univ : Finset (ZMod q)).erase 0, L (α, 0)) *
      ∏ β ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∏ α : ZMod q, L (α, β) := by
    rw [hSg, Fintype.prod_prod_type]
    have e1 : ∀ α : ZMod q, ∏ β : ZMod q, g (α, β) = g (α, 0) * ∏ β ∈ (Finset.univ : Finset (ZMod q)).erase 0, L (α, β) := by
      intro α
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod q))]
      congr 1
      refine Finset.prod_congr rfl fun β hβ => ?_
      rw [hg]; beta_reduce; rw [if_neg]
      intro h; exact Finset.ne_of_mem_erase hβ (congrArg Prod.snd h)
    simp_rw [e1]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod q)), show g ((0 : ZMod q), (0 : ZMod q)) = 1 from if_pos rfl,
      one_mul]
    refine Finset.prod_congr rfl fun α hα => ?_
    rw [hg]; beta_reduce; rw [if_neg]
    intro h; exact Finset.ne_of_mem_erase hα (congrArg Prod.fst h)

  have haxis : ∀ α : ZMod q, ∀ hα : α ≠ 0, L (α, 0) = x₀ * wfun (⟨α.val, hval α hα⟩, ⟨x₀, hx₀⟩) := by
    intro α hα
    rw [← hweq (⟨α.val, hval α hα⟩, ⟨x₀, hx₀⟩), hL]
    show ℓ α.val (0 : ZMod q).val = _
    rw [ZMod.val_zero, hℓdef, FormalGroup.evalNSMul_zero]
    exact (hzero _ (hNmem _ _ hx₀)).1

  have hline : ∀ β : ZMod q, ∀ hβ : β ≠ 0, ∏ α : ZMod q, L (α, β)
      = (∏ α : ZMod q, P α) * ∏ α : ZMod q, wfun (⟨β.val, hval β hβ⟩, ⟨P α, hPmem α⟩) := by
    intro β hβ
    rw [← Finset.prod_mul_distrib, ← ((mul_left_injective₀ hβ).bijective_of_finite).prod_comp (fun α : ZMod q => L (α, β))]
    refine Fintype.prod_congr _ _ fun α => ?_
    have hβv : β.val = (β.val * 1) % q := by rw [mul_one, Nat.mod_eq_of_lt (ZMod.val_lt β)]
    rw [← hweq (⟨β.val, hval β hβ⟩, ⟨P α, hPmem α⟩), hL]
    show ℓ (α * β).val β.val = F.evalNSMul β.val (ℓ α.val 1)
    rw [ZMod.val_mul, mul_comm α.val, ← hscale β.val α.val 1, ← hβv]

  set W0 : R := ∏ α ∈ (Finset.univ : Finset (ZMod q)).erase 0,
    (if h : α ≠ 0 then wfun (⟨α.val, hval α h⟩, ⟨x₀, hx₀⟩) else 1) with hW0
  set W1 : R := ∏ β ∈ (Finset.univ : Finset (ZMod q)).erase 0,
    (if h : β ≠ 0 then ∏ α : ZMod q, wfun (⟨β.val, hval β h⟩, ⟨P α, hPmem α⟩) else 1) with hW1
  have hcard : ((Finset.univ : Finset (ZMod q)).erase 0).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have haxisP : ∏ α ∈ (Finset.univ : Finset (ZMod q)).erase 0, L (α, 0) = x₀ ^ (q - 1) * W0 := by
    rw [hW0, ← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun α hα => ?_
    have hα0 : α ≠ 0 := Finset.ne_of_mem_erase hα
    rw [dif_pos hα0, haxis α hα0]
  have hlinesP : ∏ β ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∏ α : ZMod q, L (α, β)
      = (∏ α : ZMod q, P α) ^ (q - 1) * W1 := by
    rw [hW1, ← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun β hβ => ?_
    have hβ0 : β ≠ 0 := Finset.ne_of_mem_erase hβ
    rw [dif_pos hβ0, hline β hβ0]
  have hW0u : IsUnit W0 := by
    rw [hW0]; refine hUprod _ _ fun α hα => ?_
    rw [dif_pos (Finset.ne_of_mem_erase hα)]; exact hwunit _
  have hW1u : IsUnit W1 := by
    rw [hW1]; refine hUprod _ _ fun β hβ => ?_
    rw [dif_pos (Finset.ne_of_mem_erase hβ)]
    exact Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one (fun α _ => hwunit _)
  have hU0 : IsUnit (PowerSeries.constantCoeff U) := PowerSeries.isUnit_iff_constantCoeff.mp hU
  refine ⟨PowerSeries.constantCoeff U * (-1) ^ S.card * (W0 * W1), (hU0.mul ((isUnit_one.neg).pow _)).mul (hW0u.mul hW1u), P,
    hPlin, ?_⟩
  rw [hcoef, Finset.prod_neg, hsplit, haxisP, hlinesP]
  ring

end S_FormalGroup_IsDrinfeldBasisAdic_exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete (solution)
