-- Prove2me | solution 1 for CuspForm.eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/932cdd64-819a-54b8-bb69-9ab7a3804d40

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_qExpansion_heckeTLin
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CongruenceSubgroup ModularFormClass

noncomputable section

namespace P2mS17A1

variable {N : ℕ} [NeZero N]

abbrev S2 (N : ℕ) : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2

def fullC (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (S2 N)) :=
  Algebra.adjoin ℂ (CuspForm.heckeGenerators N 2 (∅ : Set ℕ))

scoped instance fullC.instIsMulCommutative : IsMulCommutative (fullC N) :=
  Algebra.isMulCommutative_adjoin ℂ fun _ hT _ hT' => CuspForm.commute_of_mem_heckeGenerators hT hT'

p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.P2mS17A1.fullC"
open scoped IsMulCommutative in
scoped instance fullC.instCommRing : CommRing (fullC N) := inferInstance

p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.P2mS17A1.fullC"
scoped instance fullC.instModuleFinite : Module.Finite ℂ (fullC N) := by
  haveI := CuspForm.finiteDimensional_Gamma0 N 2
  exact Module.Finite.of_injective (fullC N).val.toLinearMap Subtype.val_injective

p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.P2mS17A1.fullC"

theorem span_heckeAlgebra_eq_fullC :
    Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (S2 N)))
      = Subalgebra.toSubmodule (fullC N) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro T hT
    have hle : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) ≤ (fullC N).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro x hx
      exact (Algebra.subset_adjoin hx : x ∈ fullC N)
    exact (hle hT : T ∈ fullC N)
  · rw [fullC, Algebra.adjoin_eq_span]
    apply Submodule.span_mono
    intro T hT
    change T ∈ CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)
    exact (Submonoid.closure_le.mpr (fun x hx => Algebra.subset_adjoin hx)) hT

theorem qCoeff_heckeTLin {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (f : S2 N) (n : ℕ) :
    qCoeff (⇑(CuspForm.heckeTLin 2 hp hpN f)) n
      = qCoeff (⇑f) (p * n) + (p : ℂ) * (if p ∣ n then qCoeff (⇑f) (n / p) else 0) := by
  unfold qCoeff
  rw [CuspForm.qExpansion_heckeTLin hp hpN f, PowerSeries.coeff_heckeT]
  simp

theorem qCoeff_heckeULin {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (f : S2 N) (n : ℕ) :
    qCoeff (⇑(CuspForm.heckeULin 2 hpN f)) n = qCoeff (⇑f) (n * p) := by
  rw [CuspForm.coe_heckeULin_apply]
  rw [ModularFormClass.qCoeff_heckeU f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) hp.ne_zero n,
    ModularForm.coeffHeckeU_apply]

def formKer (N : ℕ) [NeZero N] : Set (S2 N) :=
  {f | ∀ T ∈ fullC N, qCoeff (⇑(T f)) 1 = 0}

theorem formKer_stable {f : S2 N} (hf : f ∈ formKer N) {S : Module.End ℂ (S2 N)} (hS : S ∈ fullC N) :
    S f ∈ formKer N := by
  intro T hT
  have h : (T * S) f = T (S f) := rfl
  rw [← h]
  exact hf _ ((fullC N).mul_mem hT hS)

theorem qCoeff_eq_zero_of_mem_formKer : ∀ (n : ℕ) (f : S2 N), f ∈ formKer N → qCoeff (⇑f) n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact CuspForm.qCoeff_zero f
      · simpa using hf 1 (fullC N).one_mem
    ·
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm : m < p * m := by
        have := hp.one_lt
        have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
      by_cases hpN : p ∣ N
      ·
        have hU : CuspForm.heckeULin 2 hpN f ∈ formKer N :=
          formKer_stable hf (Algebra.subset_adjoin (CuspForm.heckeULin_mem_heckeGenerators hp hpN (by simp)))
        have := ih m hm _ hU
        rw [qCoeff_heckeULin hp hpN] at this
        rwa [mul_comm] at this
      ·
        have hT : CuspForm.heckeTLin 2 hp hpN f ∈ formKer N :=
          formKer_stable hf (Algebra.subset_adjoin (CuspForm.heckeTLin_mem_heckeGenerators hp hpN (by simp)))
        have h1 := ih m hm _ hT
        rw [qCoeff_heckeTLin hp hpN] at h1
        have h2 : (if p ∣ m then qCoeff (⇑f) (m / p) else 0) = 0 := by
          split_ifs with hpm
          · exact ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hm) f hf
          · rfl
        rw [h2, mul_zero, add_zero] at h1
        exact h1

theorem eq_zero_of_mem_formKer {f : S2 N} (hf : f ∈ formKer N) : f = 0 := by
  refine ModularFormClass.eq_of_forall_qCoeff_eq (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) fun n => ?_
  rw [qCoeff_eq_zero_of_mem_formKer n f hf]
  show (0 : ℂ) = qCoeff (⇑(0 : S2 N)) n
  rw [CuspForm.coe_zero]
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero]

theorem qCoeff_add' (f g : S2 N) (n : ℕ) : qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.coe_add]

  first
    | rw [ModularForm.qExpansion_add one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]
    | rw [ModularFormClass.qExpansion_add one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]

theorem qCoeff_smul' (c : ℂ) (f : S2 N) (n : ℕ) : qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  unfold qCoeff

  rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl]
  first
    | rw [ModularForm.qExpansion_smul one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) c f, map_smul, smul_eq_mul]
    | rw [ModularFormClass.qExpansion_smul one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) c f, map_smul, smul_eq_mul]

def a1Pairing (N : ℕ) [NeZero N] : fullC N →ₗ[ℂ] S2 N →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun T f => qCoeff (⇑((T : Module.End ℂ (S2 N)) f)) 1)
    (fun T S f => by
      show qCoeff (⇑(((T : Module.End ℂ (S2 N)) + (S : Module.End ℂ (S2 N))) f)) 1 = _
      rw [LinearMap.add_apply, qCoeff_add'])
    (fun c T f => by
      show qCoeff (⇑((c • (T : Module.End ℂ (S2 N))) f)) 1 = _
      rw [LinearMap.smul_apply, qCoeff_smul', smul_eq_mul])
    (fun T f g => by
      show qCoeff (⇑((T : Module.End ℂ (S2 N)) (f + g))) 1 = _
      rw [map_add, qCoeff_add'])
    (fun c T f => by
      show qCoeff (⇑((T : Module.End ℂ (S2 N)) (c • f))) 1 = _
      rw [map_smul, qCoeff_smul', smul_eq_mul])

@[scoped simp] theorem a1Pairing_apply (T : fullC N) (f : S2 N) :
    a1Pairing N T f = qCoeff (⇑((T : Module.End ℂ (S2 N)) f)) 1 := rfl

def a1PairingDual (N : ℕ) [NeZero N] : S2 N →ₗ[ℂ] Module.Dual ℂ (fullC N) := (a1Pairing N).flip

theorem a1PairingDual_injective : Function.Injective (a1PairingDual N) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply eq_zero_of_mem_formKer
  intro T hT
  have := congrArg (fun ψ : Module.Dual ℂ (fullC N) => ψ ⟨T, hT⟩) hf
  simpa [a1PairingDual] using this

theorem eq_zero_of_mem_fullC_of_forall_qCoeff_one_eq_zero {T : Module.End ℂ (S2 N)} (hT : T ∈ fullC N)
    (h : ∀ f : S2 N, qCoeff (⇑(T f)) 1 = 0) : T = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  apply eq_zero_of_mem_formKer
  intro S hS
  have hcomm : S * T = T * S :=
    congrArg Subtype.val (mul_comm (⟨S, hS⟩ : fullC N) ⟨T, hT⟩)
  have : S (T f) = T (S f) := by
    change (S * T) f = (T * S) f
    rw [hcomm]
  rw [this]
  exact h (S f)

theorem a1Pairing_injective : Function.Injective (a1Pairing N) := by
  rw [injective_iff_map_eq_zero]
  intro T hT
  apply Subtype.ext
  refine eq_zero_of_mem_fullC_of_forall_qCoeff_one_eq_zero T.2 fun f => ?_
  have := congrArg (fun ψ : S2 N →ₗ[ℂ] ℂ => ψ f) hT
  simpa using this

theorem finrank_fullC_eq_finrank_cuspForm :
    Module.finrank ℂ (fullC N) = Module.finrank ℂ (S2 N) := by
  haveI := CuspForm.finiteDimensional_Gamma0 N 2
  refine le_antisymm ?_ ?_
  · have h1 : Module.finrank ℂ (fullC N) ≤ Module.finrank ℂ (Module.Dual ℂ (S2 N)) :=
      LinearMap.finrank_le_finrank_of_injective a1Pairing_injective
    rwa [Subspace.dual_finrank_eq] at h1
  · have h2 : Module.finrank ℂ (S2 N) ≤ Module.finrank ℂ (Module.Dual ℂ (fullC N)) :=
      LinearMap.finrank_le_finrank_of_injective a1PairingDual_injective
    rwa [Subspace.dual_finrank_eq] at h2

theorem a1PairingDual_surjective : Function.Surjective (a1PairingDual N) := by
  haveI := CuspForm.finiteDimensional_Gamma0 N 2
  have hdim : Module.finrank ℂ (S2 N) = Module.finrank ℂ (Module.Dual ℂ (fullC N)) := by
    rw [Subspace.dual_finrank_eq, finrank_fullC_eq_finrank_cuspForm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp a1PairingDual_injective

theorem exists_realizing_form_of_dual (ψ : Module.Dual ℂ (fullC N)) :
    ∃ f : S2 N, ∀ (T : Module.End ℂ (S2 N)) (hT : T ∈ fullC N), ψ ⟨T, hT⟩ = qCoeff (⇑(T f)) 1 := by
  obtain ⟨f, hf⟩ := a1PairingDual_surjective ψ
  exact ⟨f, fun T hT => by rw [← hf]; rfl⟩

end P2mS17A1
p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.P2mS17A1.fullC P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero.P2mS17A1"

theorem solution (N : ℕ) [NeZero N] (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (hT : T ∈ Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))))
    (h : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ModularFormClass.qCoeff (T f) 1 = 0) :
    T = 0 := by
  have hT' : T ∈ P2mS17A1.fullC N := by
    have := (P2mS17A1.span_heckeAlgebra_eq_fullC (N := N)) ▸ hT
    exact this
  exact P2mS17A1.eq_zero_of_mem_fullC_of_forall_qCoeff_one_eq_zero hT' h

end
end S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
end P2MW
export P2MW.S_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero (solution)
