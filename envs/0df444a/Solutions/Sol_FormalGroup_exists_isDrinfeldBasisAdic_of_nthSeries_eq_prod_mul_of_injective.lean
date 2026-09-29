-- Prove2me | solution 1 for FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4a87facc-2707-502d-8dbc-65f9aa3450f7

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Theorems.Thm_FormalGroup_evalSeries_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DW2B3

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

end Values

end DW2B3

namespace DW2B3

theorem prod_range_range_eq_prod_prod {M : Type*} [CommMonoid M] (q : ℕ) (f : ℕ → ℕ → M) :
    ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, f a b = ∏ p : Fin q × Fin q, f p.1 p.2 := by
  rw [Fintype.prod_prod_type, ← Fin.prod_univ_eq_prod_range (fun a => ∏ b ∈ Finset.range q, f a b)]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact (Fin.prod_univ_eq_prod_range (f a) q).symm

theorem coe_prod_X_sub_C {V : Type*} [CommRing V] {ι : Type*} [Fintype ι] (r : ι → V) :
    ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) =
      ∏ i, (PowerSeries.X - PowerSeries.C (r i)) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

end DW2B3

namespace DW2B3

@[reducible] noncomputable def subsetGroup {V : Type*} [CommRing V] [UniformSpace V] (G : FormalGroup V) (S : Set V) (q : ℕ)
    (hadd : ∀ x y : V, x ∈ S → y ∈ S → G.eval x y ∈ S) (h0 : (0 : V) ∈ S)
    (hN : ∀ (n : ℕ) (x : V), x ∈ S → G.evalNSMul n x ∈ S)
    (hassoc : ∀ x y z : V, x ∈ S → y ∈ S → z ∈ S → G.eval (G.eval x y) z = G.eval x (G.eval y z))
    (hcomm : ∀ x y : V, x ∈ S → y ∈ S → G.eval x y = G.eval y x)
    (hzero : ∀ x : V, x ∈ S → G.eval x 0 = x ∧ G.eval 0 x = x)
    (hneg : ∀ x : V, x ∈ S → G.eval (G.evalNSMul (q - 1) x) x = 0) : AddCommGroup ↥S :=
  { add := fun s t => ⟨G.eval s.1 t.1, hadd _ _ s.2 t.2⟩
    add_assoc := fun s t u => Subtype.ext (hassoc _ _ _ s.2 t.2 u.2)
    zero := ⟨0, h0⟩
    zero_add := fun s => Subtype.ext (hzero _ s.2).2
    add_zero := fun s => Subtype.ext (hzero _ s.2).1
    nsmul := fun n s => ⟨G.evalNSMul n s.1, hN n _ s.2⟩
    nsmul_zero := fun s => rfl
    nsmul_succ := fun n s => rfl
    add_comm := fun s t => Subtype.ext (hcomm _ _ s.2 t.2)
    neg := fun s => ⟨G.evalNSMul (q - 1) s.1, hN _ _ s.2⟩
    zsmul := @zsmulRec ↥S ⟨⟨0, h0⟩⟩ ⟨fun s t => ⟨G.eval s.1 t.1, hadd _ _ s.2 t.2⟩⟩
      ⟨fun s => ⟨G.evalNSMul (q - 1) s.1, hN _ _ s.2⟩⟩ (fun n s => ⟨G.evalNSMul n s.1, hN n _ s.2⟩)
    zsmul_zero' := fun s => rfl
    zsmul_succ' := fun n s => rfl
    zsmul_neg' := fun n s => rfl
    neg_add_cancel := fun s => Subtype.ext (hneg _ s.2) }

end DW2B3

set_option maxHeartbeats 8000000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (G : FormalGroup V) [G.IsComm]
    (r : Fin (q * q) → V) (hr : ∀ i, r i ∈ maximalIdeal V) (hinj : Function.Injective r)
    (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) * U) :
    ∃ α β : V, α ∈ maximalIdeal V ∧ β ∈ maximalIdeal V ∧ G.IsDrinfeldBasisAdic (maximalIdeal V) q α β := by
  classical
  letI W : WithIdeal V := ⟨maximalIdeal V⟩
  have HI : IsAdic (maximalIdeal V) := rfl
  obtain ⟨hcs, ht2⟩ := HI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal V) V)
  haveI := hcs
  haveI := ht2
  set 𝔪 := maximalIdeal V with h𝔪
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  have hmem : ∀ x y : V, x ∈ 𝔪 → y ∈ 𝔪 → G.eval x y ∈ 𝔪 := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2B3.eval₂_mem V _ ⊥ inferInstance V _ _ 𝔪 _ (Fin 2) _ ![x, y]
      (fun s => by fin_cases s <;> simp [hx, hy]) G.toPowerSeries
      (by rw [G.zero_constantCoeff, map_zero]; exact Submodule.zero_mem _)
  have hcomm : ∀ x y : V, x ∈ 𝔪 → y ∈ 𝔪 → G.eval x y = G.eval y x := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @DW2B3.eval₂_comm V _ ⊥ inferInstance V _ _ 𝔪 _ G _ x y hx hy
  have hassoc : ∀ x y z : V, x ∈ 𝔪 → y ∈ 𝔪 → z ∈ 𝔪 →
      G.eval (G.eval x y) z = G.eval x (G.eval y z) := by
    intro x y z hx hy hz
    unfold FormalGroup.eval
    exact @DW2B3.eval₂_assoc V _ ⊥ inferInstance V _ _ 𝔪 _ G x y z hx hy hz
  have hzero : ∀ x : V, x ∈ 𝔪 → G.eval x 0 = x ∧ G.eval 0 x = x := by
    intro x hx
    unfold FormalGroup.eval
    exact @DW2B3.eval₂_pair_zero V _ ⊥ inferInstance V _ _ 𝔪 _ G x hx

  have hNmem : ∀ (n : ℕ) (x : V), x ∈ 𝔪 → G.evalNSMul n x ∈ 𝔪 := by
    intro n x hx
    induction n with
    | zero => exact Submodule.zero_mem _
    | succ n ih => rw [FormalGroup.evalNSMul_succ]; exact hmem _ _ ih hx
  have hN0 : ∀ n : ℕ, G.evalNSMul n (0 : V) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [FormalGroup.evalNSMul_succ, ih]; exact (hzero 0 (Submodule.zero_mem _)).1
  have hNadd : ∀ (n : ℕ) (x y : V), x ∈ 𝔪 → y ∈ 𝔪 →
      G.evalNSMul n (G.eval x y) = G.eval (G.evalNSMul n x) (G.evalNSMul n y) := by
    intro n x y hx hy
    induction n with
    | zero => simp only [FormalGroup.evalNSMul_zero]; exact (hzero 0 (Submodule.zero_mem _)).1.symm
    | succ n ih =>
      rw [FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, ih]
      have h1 := hNmem n x hx
      have h2 := hNmem n y hy
      rw [hassoc _ _ _ h1 h2 (hmem _ _ hx hy), ← hassoc _ _ _ h2 hx hy, hcomm _ _ h2 hx,
        hassoc _ _ _ hx h2 hy, ← hassoc _ _ _ h1 hx (hmem _ _ h2 hy)]
  have hNaddExp : ∀ (m n : ℕ) (x : V), x ∈ 𝔪 →
      G.evalNSMul (m + n) x = G.eval (G.evalNSMul m x) (G.evalNSMul n x) := by
    intro m n x hx
    induction n with
    | zero => rw [_root_.add_zero, FormalGroup.evalNSMul_zero]; exact (hzero _ (hNmem m x hx)).1.symm
    | succ n ih =>
      rw [← add_assoc, FormalGroup.evalNSMul_succ, FormalGroup.evalNSMul_succ, ih,
        hassoc _ _ _ (hNmem m x hx) (hNmem n x hx) hx]
  have hNmul : ∀ (m n : ℕ) (x : V), x ∈ 𝔪 → G.evalNSMul n (G.evalNSMul m x) = G.evalNSMul (m * n) x := by
    intro m n x hx
    induction n with
    | zero => rfl
    | succ n ih => rw [FormalGroup.evalNSMul_succ, ih, Nat.mul_succ, hNaddExp _ _ _ hx]

  have hPeval : ∀ x : V, (∏ i, (Polynomial.X - Polynomial.C (r i))).eval x = 0 ↔ x ∈ Set.range r := by
    intro x
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩
    · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩
  have hroot : ∀ x : V, x ∈ 𝔪 → (G.evalNSMul q x = 0 ↔ x ∈ Set.range r) := by
    intro x hx
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal V) x hx
    have h1 : G.evalNSMul q x = e (G.nthSeries q) := by
      rw [← he, FormalGroup.evalSeries_nthSeries G (WithIdeal.isTopologicallyNilpotent_of_mem hx) q]
    rw [h1, hq, map_mul, hep, (hU.map e).mul_left_eq_zero, hPeval]

  have hr𝔪 : ∀ x : V, x ∈ Set.range r → x ∈ 𝔪 := by rintro x ⟨i, rfl⟩; exact hr i
  have hS0 : (0 : V) ∈ Set.range r := (hroot 0 (Submodule.zero_mem _)).mp (hN0 q)
  have hSadd : ∀ x y : V, x ∈ Set.range r → y ∈ Set.range r → G.eval x y ∈ Set.range r := by
    intro x y hx hy
    refine (hroot _ (hmem _ _ (hr𝔪 x hx) (hr𝔪 y hy))).mp ?_
    rw [hNadd _ _ _ (hr𝔪 x hx) (hr𝔪 y hy), (hroot x (hr𝔪 x hx)).mpr hx, (hroot y (hr𝔪 y hy)).mpr hy]
    exact (hzero 0 (Submodule.zero_mem _)).1
  have hSN : ∀ (n : ℕ) (x : V), x ∈ Set.range r → G.evalNSMul n x ∈ Set.range r := by
    intro n x hx
    induction n with
    | zero => exact hS0
    | succ n ih => rw [FormalGroup.evalNSMul_succ]; exact hSadd _ _ ih hx
  have hSneg : ∀ x : V, x ∈ Set.range r → G.eval (G.evalNSMul (q - 1) x) x = 0 := by
    intro x hx
    rw [← FormalGroup.evalNSMul_succ, Nat.sub_add_cancel hq1]
    exact (hroot _ (hr𝔪 _ hx)).mpr hx
  letI iS : AddCommGroup ↥(Set.range r) := DW2B3.subsetGroup G (Set.range r) q hSadd hS0 hSN
    (fun x y z hx hy hz => hassoc x y z (hr𝔪 _ hx) (hr𝔪 _ hy) (hr𝔪 _ hz))
    (fun x y hx hy => hcomm x y (hr𝔪 _ hx) (hr𝔪 _ hy)) (fun x hx => hzero x (hr𝔪 _ hx)) hSneg
  have val_add : ∀ s t : ↥(Set.range r), (s + t).1 = G.eval s.1 t.1 := fun _ _ => rfl
  have val_nsmul : ∀ (n : ℕ) (s : ↥(Set.range r)), (n • s).1 = G.evalNSMul n s.1 := fun _ _ => rfl
  have hqS : ∀ s : ↥(Set.range r), q • s = 0 := fun s => Subtype.ext ((hroot _ (hr𝔪 _ s.2)).mpr s.2)
  haveI iM : Module (ZMod q) ↥(Set.range r) := AddCommGroup.zmodModule hqS
  haveI : Fintype ↥(Set.range r) := Set.fintypeRange r
  have hcardS : Fintype.card ↥(Set.range r) = q * q := by
    rw [Set.card_range_of_injective hinj, Fintype.card_fin]

  have hrank : Module.finrank (ZMod q) ↥(Set.range r) = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := ↥(Set.range r))
    rw [hcardS, ZMod.card] at h
    have h' : q ^ 2 = q ^ Module.finrank (ZMod q) ↥(Set.range r) := by rw [pow_two]; exact h
    exact (Nat.pow_right_injective hq2 h').symm
  haveI instMF : Module.Finite (ZMod q) ↥(Set.range r) := Module.Finite.of_finite
  haveI instFr : Module.Free (ZMod q) ↥(Set.range r) := Module.Free.of_divisionRing (ZMod q) ↥(Set.range r)
  let bs : Module.Basis (Fin 2) (ZMod q) ↥(Set.range r) := @Module.finBasisOfFinrankEq (ZMod q) ↥(Set.range r) _ _ _ instFr _ instMF 2 hrank

  let g : Fin q × Fin q → ↥(Set.range r) := fun p => (p.1 : ℕ) • bs 0 + (p.2 : ℕ) • bs 1
  have hg_repr : ∀ p : Fin q × Fin q, bs.repr (g p) 0 = (p.1 : ℕ) ∧ bs.repr (g p) 1 = (p.2 : ℕ) := by
    intro p
    simp only [g, ← Nat.cast_smul_eq_nsmul (ZMod q), map_add, map_smul, bs.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply]
    simp
  have hginj : Function.Injective g := by
    intro p p' h
    have h0 := (hg_repr p).1; have h1 := (hg_repr p).2
    rw [h] at h0 h1
    rw [(hg_repr p').1] at h0; rw [(hg_repr p').2] at h1
    have e1 : (p'.1 : ℕ) = p.1 := by
      have := congrArg ZMod.val h0; rwa [ZMod.val_cast_of_lt p'.1.isLt, ZMod.val_cast_of_lt p.1.isLt] at this
    have e2 : (p'.2 : ℕ) = p.2 := by
      have := congrArg ZMod.val h1; rwa [ZMod.val_cast_of_lt p'.2.isLt, ZMod.val_cast_of_lt p.2.isLt] at this
    exact Prod.ext (Fin.ext e1.symm) (Fin.ext e2.symm)
  have hgbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hginj, by rw [Fintype.card_prod, Fintype.card_fin, hcardS]⟩
  let ρ : Fin (q * q) → ↥(Set.range r) := fun i => ⟨r i, ⟨i, rfl⟩⟩
  have hρbij : Function.Bijective ρ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun i j h => hinj (congrArg Subtype.val h), by rw [Fintype.card_fin, hcardS]⟩

  refine ⟨(bs 0).1, (bs 1).1, hr𝔪 _ (bs 0).2, hr𝔪 _ (bs 1).2, ?_⟩
  rw [FormalGroup.isDrinfeldBasisAdic_iff]
  refine ⟨U, hU, ?_⟩
  have hdiv : G.drinfeldDivisorAdic (maximalIdeal V) q (bs 0).1 (bs 1).1 =
      ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) := by
    show (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
        (PowerSeries.X - PowerSeries.C (G.linComb (bs 0).1 (bs 1).1 a b))) = _
    rw [DW2B3.prod_range_range_eq_prod_prod q (fun a b => PowerSeries.X - PowerSeries.C (G.linComb (bs 0).1 (bs 1).1 a b)),
      DW2B3.coe_prod_X_sub_C r,
      Fintype.prod_bijective g hgbij
        (fun p => PowerSeries.X - PowerSeries.C (G.linComb (bs 0).1 (bs 1).1 p.1 p.2))
        (fun s => PowerSeries.X - PowerSeries.C s.1) (fun p => rfl),
      ← Fintype.prod_bijective ρ hρbij (fun i => PowerSeries.X - PowerSeries.C (r i))
        (fun s => PowerSeries.X - PowerSeries.C s.1) (fun i => rfl)]
  rw [hdiv, mul_comm]
  exact hq

end S_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
end P2MW
export P2MW.S_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective (solution)
