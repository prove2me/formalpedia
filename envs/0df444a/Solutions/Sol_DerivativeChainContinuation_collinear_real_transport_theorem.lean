-- Prove2me | solution 1 for DerivativeChainContinuation.collinear_real_transport_theorem
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:48:42.952989+00:00
-- url     : https://prove2.me/submissions/fc08145b-d148-4262-b8c7-d84b9b67e31e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_collinear_transport_chain_family
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0<n)
    (a : Fin (n+1) → ℝ) (o c : ℂ) (hc : c≠0)
    (hvariance : 0 < ∑ i,‖o+c*(a i : ℂ)-complexCentroid (fun j => o+c*(a j : ℂ))‖^2) :
    uniformComplexTransportRatio (fun i => o+c*(a i : ℂ)) ≤ (28/3 : ℝ) := by
  obtain ⟨z,hz,he,hcost⟩ := collinear_transport_chain_family n hn a o c hc
  unfold uniformComplexTransportRatio
  apply (div_le_iff₀ hvariance).mpr
  apply le_trans _ hcost
  apply Finset.sum_le_sum
  intro i _
  have hnonneg (w : Fin (n+1) → ℂ) : 0 ≤ chainCost w :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : ∀ t∈{t : ℝ | ∃ w : Fin (n+1) → ℂ,
      IsChain (fun j => o+c*(a j : ℂ)) w ∧ w (Fin.last n)=o+c*(a i : ℂ) ∧ chainCost w=t},0≤t := by
    rintro t ⟨w,_,_,rfl⟩
    exact hnonneg w
  have hm : chainCost (z i) ∈ {t : ℝ | ∃ w : Fin (n+1) → ℂ,
      IsChain (fun j => o+c*(a j : ℂ)) w ∧ w (Fin.last n)=o+c*(a i : ℂ) ∧ chainCost w=t} :=
    ⟨z i,hz i,he i,rfl⟩
  have hl : 0 ≤ complexEndpointCost (fun j => o+c*(a j : ℂ)) (o+c*(a i : ℂ)) := le_csInf ⟨_,hm⟩ hb
  have hu : complexEndpointCost (fun j => o+c*(a j : ℂ)) (o+c*(a i : ℂ)) ≤ chainCost (z i) :=
    csInf_le ⟨0,hb⟩ hm
  exact (sq_le_sq₀ hl (hnonneg _)).mpr hu
