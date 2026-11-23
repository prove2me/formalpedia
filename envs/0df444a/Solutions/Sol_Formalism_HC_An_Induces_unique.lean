-- Prove2me | solution 1 for Formalism.HC.An.Induces.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:24.86085+00:00
-- url     : https://prove2.me/submissions/ff2d12c9-978f-469e-9da4-711bab271059

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC
namespace An
private theorem pchar_ext_of_N_eq_of_heq (ψ ψ' : PChar) (hN : ψ.N = ψ'.N) (hχ : HEq ψ.χ ψ'.χ) : ψ = ψ' := by
  cases ψ
  cases ψ'
  cases hN
  cases hχ
  rfl
private theorem heq_of_changeLevel_eq_of_level_eq {N N' L : ℕ} [NeZero L] (χ : DirichletCharacter ℂ N)
    (χ' : DirichletCharacter ℂ N') (d1 : N ∣ L) (d2 : N' ∣ L) (hNN : N = N')
    (heq : DirichletCharacter.changeLevel d1 χ = DirichletCharacter.changeLevel d2 χ') : HEq χ χ' := by
  subst hNN
  exact heq_of_eq (DirichletCharacter.changeLevel_injective d1 heq)
end An
namespace Frame
variable (φ : Frame)
end Frame
namespace HostRaw
variable {φ : Frame} (H : HostRaw φ)
end HostRaw
end Formalism.HC
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.HC.An
namespace Formalism.HC.An
namespace Induces
theorem _root_.solution {ψ ψ' : PChar} {f : ℕ → ℂ} {M : ℕ} (hM : M ≠ 0) (h : Induces ψ.χ f M) (h' : Induces ψ'.χ f M) :
    ψ = ψ' := by
  haveI := ψ.ne
  haveI := ψ'.ne
  have hN0 : ψ.N ≠ 0 := NeZero.ne _
  have hN0' : ψ'.N ≠ 0 := NeZero.ne _
  haveI : NeZero (ψ.N * ψ'.N * M) := ⟨mul_ne_zero (mul_ne_zero hN0 hN0') hM⟩
  have d1 : ψ.N ∣ ψ.N * ψ'.N * M := ⟨ψ'.N * M, by ring⟩
  have d2 : ψ'.N ∣ ψ.N * ψ'.N * M := ⟨ψ.N * M, by ring⟩
  have heq : DirichletCharacter.changeLevel d1 ψ.χ = DirichletCharacter.changeLevel d2 ψ'.χ := by
    apply MulChar.ext
    intro u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hcop : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime (ψ.N * ψ'.N * M) := ZMod.val_coe_unit_coprime u
    have hcM : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime M :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_left M (ψ.N * ψ'.N)) hcop
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, h.2 _ hcM, h'.2 _ hcM]
  have hc : ψ.N = ψ'.N := by
    have e1 := DirichletCharacter.conductor_changeLevel ψ.χ d1
    have e2 := DirichletCharacter.conductor_changeLevel ψ'.χ d2
    rw [heq, e2] at e1
    calc ψ.N = ψ.χ.conductor := ((DirichletCharacter.isPrimitive_def ψ.χ).mp ψ.prim).symm
      _ = ψ'.χ.conductor := e1.symm
      _ = ψ'.N := (DirichletCharacter.isPrimitive_def ψ'.χ).mp ψ'.prim
  exact pchar_ext_of_N_eq_of_heq ψ ψ' hc (heq_of_changeLevel_eq_of_level_eq ψ.χ ψ'.χ d1 d2 hc heq)
end Induces
end Formalism.HC.An
