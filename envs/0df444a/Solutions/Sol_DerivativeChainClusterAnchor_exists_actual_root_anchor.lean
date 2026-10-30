-- Prove2me | solution 1 for DerivativeChainClusterAnchor.exists_actual_root_anchor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:27:40.775714+00:00
-- url     : https://prove2.me/submissions/39cafac1-2b0d-424e-9cf7-6d15f93f6d8d

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial
open DerivativeChainClusterAnchor


















theorem solution (p : ℂ[X]) (hp : p.Monic) (m : ℕ)
    (hm : 0 < m) (hdegree : p.natDegree=m) (c : ℂ) :
    ∃ z : ℂ, p.eval z=0 ∧ ‖z-c‖ ≤ ‖p.eval c‖^((m:ℝ)⁻¹) := by
  classical
  have hcard : Fintype.card p.roots=m := by
    rw [Multiset.card_coe,← (IsAlgClosed.splits p).natDegree_eq_card_roots,hdegree]
  letI : Nonempty p.roots := Fintype.card_pos_iff.mp (by rw [hcard]; exact hm)
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset p.roots)
    (fun i => ‖c-(i:ℂ)‖) Finset.univ_nonempty
  have hprod : (p.roots.map (fun z => c-z)).prod = ∏ i : p.roots, (c-(i:ℂ)) := by
    change _ = ((Finset.univ : Finset p.roots).val.map (fun i : p.roots => c-(i:ℂ))).prod
    rw [Multiset.map_univ]
  have heval : ‖p.eval c‖=∏ i : p.roots, ‖c-(i:ℂ)‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp c,hprod,norm_prod]
  have hpow : ‖c-(i:ℂ)‖^m ≤ ‖p.eval c‖ := by
    rw [heval]
    have hh := Finset.prod_le_prod (s := (Finset.univ : Finset p.roots))
      (fun _ _ => norm_nonneg (c-(i:ℂ))) (fun j _ => hi j (Finset.mem_univ j))
    simpa only [Finset.prod_const,Finset.card_univ,hcard] using hh
  have hroot : (‖p.eval c‖^((m:ℝ)⁻¹))^m=‖p.eval c‖ :=
    Real.rpow_inv_natCast_pow (norm_nonneg _) hm.ne'
  have hdist : ‖c-(i:ℂ)‖ ≤ ‖p.eval c‖^((m:ℝ)⁻¹) :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _) hm.ne').mp
      (by rw [hroot]; exact hpow)
  refine ⟨(i:ℂ),(mem_roots hp.ne_zero).mp (Multiset.coe_mem (x := i)),?_⟩
  simpa only [norm_sub_rev] using hdist
