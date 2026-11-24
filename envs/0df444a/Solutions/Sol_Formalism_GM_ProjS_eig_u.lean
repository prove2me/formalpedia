-- Prove2me | solution 1 for Formalism.GM.ProjS.eig_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:34.329141+00:00
-- url     : https://prove2.me/submissions/b03e936e-d637-4016-911c-4715bb5d94b0

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support
import Theorems.Thm_Formalism_GM_ProjS_eulL_mul
import Theorems.Thm_Formalism_GM_ProjS_eulL_X_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
section
variable {s : ℕ} {w e : Fin s → σ}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
section
variable {o n z : ℕ} {y : MvPolynomial σ k}
private theorem eulL_X_pow_mul_eq_smul {q : ℕ} (t : Fin q → σ) (x0 : σ) (d a b : ℕ) (f : MvPolynomial σ k)
    (ha : ∑ c, (Finsupp.single x0 d) (t c) = a) (hb : ∀ m ∈ f.support, ∑ c, m (t c) = b) :
    eulL t (X x0 ^ d * f) = ((a + b : ℕ) : k) • (X x0 ^ d * f) := by
  rw [eulL_mul, eulL_X_pow t x0 d a ha, eulL_of_support t b f hb, smul_mul_assoc,
    mul_smul_comm, ← add_smul, Nat.cast_add]
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
variable {o n z : ℕ} {y : MvPolynomial σ k}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) (X zv ^ z * y) = ((o + z : ℕ) : k) • (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) (X zv ^ z * y) = (n : k) • (X zv ^ z * y) ∧
    eulL w (X zv ^ z * y) = (o : k) • (X zv ^ z * y) := by
  obtain ⟨hw, he, hwe, hzz, hzs⟩ := hv
  have n1 : ∀ c, zv ≠ w c := fun c => (hzz c).1.symm
  have n2 : ∀ c, zv ≠ e c := fun c => (hzz c).2.2.1.symm
  refine ⟨?_, ?_, ?_⟩
  · have h := eulL_X_pow_mul_eq_smul (k := k) (Fin.cons zv w : Fin (r + 1) → σ) zv z z o y ?_ ?_
    · rwa [add_comm z o] at h
    · rw [Fin.sum_univ_succ]
      simp [n1]
    · intro m hm
      rw [Fin.sum_univ_succ]
      simp [(hz m hm).1, (hy m hm).1]
  · have h := eulL_X_pow_mul_eq_smul (k := k) (Fin.cons sv e : Fin (r + 1) → σ) zv z 0 n y ?_ ?_
    · rwa [zero_add] at h
    · rw [Fin.sum_univ_succ]
      simp [n2, hzs]
    · intro m hm
      rw [Fin.sum_univ_succ]
      simp [(hz m hm).2, (hy m hm).2]
  · have h := eulL_X_pow_mul_eq_smul (k := k) w zv z 0 o y ?_ ?_
    · rwa [zero_add] at h
    · simp [n1]
    · intro m hm
      exact (hy m hm).1
end Formalism.GM.ProjS
