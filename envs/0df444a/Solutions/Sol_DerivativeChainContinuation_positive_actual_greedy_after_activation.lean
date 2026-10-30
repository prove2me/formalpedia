-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_greedy_after_activation
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:51:47.364399+00:00
-- url     : https://prove2.me/submissions/e6897c1b-5d7f-4c5e-b245-8fdd6a20a829

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_actual_activation_roots
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_step
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp
























end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem complexHistoryOf_root {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hz : DerivativeChainPrivate.IsChain a z) (j : ℕ) (hj : j ≤ n) :
    (row a (j+1)).eval (complexHistoryOf z j)=0 := by
  simpa only [complexHistoryOf,dif_pos (show j<n+1 by omega)] using hz ⟨j,by omega⟩











end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial







theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring









end DerivativeChainPrivate

theorem solution {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (hz : IsGreedyChain a z) :
    ∀ m : ℕ,k ≤ m → m ≤ n+1 →
      complexHistoryOf z (m-1)≠0 ∧
        (∀ w : ℂ,(row a m).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z (m-1)‖) ∧
        ∃ c : ℝ,1 ≤ c ∧ complexHistoryOf z (m-1)=(c : ℂ)*complexHistoryOf z (k-1) := by
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  obtain ⟨b,hb,hactivation⟩ := positive_actual_activation_roots a k r Q hk hQ hQdegree hp
  have hinvariant (j : ℕ) (hj : k+j ≤ n+1) :
      complexHistoryOf z (k+j-1)≠0 ∧
        (∀ w : ℂ,(row a (k+j)).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z (k+j-1)‖) ∧
        ∃ c : ℝ,1 ≤ c ∧ complexHistoryOf z (k+j-1)=(c : ℂ)*complexHistoryOf z (k-1) := by
    induction j with
    | zero =>
      have hroot : (row a k).eval (complexHistoryOf z (k-1))=0 := by
        have h := complexHistoryOf_root a z hz.1 (k-1) (by omega)
        rwa [show k-1+1=k by omega] at h
      have hpower := (hactivation _).mp hroot
      have hnonzero : complexHistoryOf z (k-1)≠0 := by
        intro he
        rw [he,zero_pow (show k≠0 by omega)] at hpower
        have hb0 : b=0 := Complex.ofReal_injective hpower.symm
        linarith
      refine ⟨hnonzero,?_,⟨1,le_rfl,by simp⟩⟩
      intro w hw
      have hwpow := (hactivation w).mp hw
      have hnorm : ‖w‖^k=‖complexHistoryOf z (k-1)‖^k := by rw [←norm_pow,←norm_pow,hwpow,hpower]
      exact ((pow_left_inj₀ (norm_nonneg w) (norm_nonneg _) (show k≠0 by omega)).mp hnorm).le
    | succ j ih =>
      obtain ⟨hw,hmax,c,hc,hform⟩ := ih (by omega)
      obtain ⟨hnew,hnewmax,d,hd,hnewform⟩ := positive_actual_greedy_step a z k r Q hk hQ hQdegree hp hz
        (k+j) (by omega) (by omega) hw hmax
      have heidx : k+(j+1)-1=k+j := by omega
      rw [heidx]
      refine ⟨hnew,?_,⟨d*c,by nlinarith,?_⟩⟩
      · simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hnewmax
      · rw [hnewform,hform,Complex.ofReal_mul]
        ring
  intro m hm hmn
  have h := hinvariant (m-k) (by omega)
  simpa only [show k+(m-k)=m by omega] using h
