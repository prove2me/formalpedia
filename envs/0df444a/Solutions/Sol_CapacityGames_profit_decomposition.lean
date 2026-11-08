-- Prove2me | solution 1 for CapacityGames.profit_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:17:39.241167+00:00
-- url     : https://prove2.me/submissions/c57edb4e-84be-4db1-99ec-d963250fbe15

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

open CapacityGames in
theorem solution {N Ω : Type*} [Fintype N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid) (B : N → Bid N) (p : Choice N Ω)
    (hp : BidFeasible G B p) :
    scProfit G p = buyerProfit G B p + ∑ i, supplierProfit G B i p := by
  haveI := hG.prob
  have hV := hp.1.2.2.1
  have hC := hp.1.2.2.2
  have hP := hp.2
  have hbuy : Integrable
      (fun D => G.V D (p.s D) - ∑ i, ((B i).P (p.s D) + (B i).R p.t)) G.μ :=
    hV.sub (integrable_finsetSum _ (fun i _ => (hP i).add (integrable_const _)))
  have hsup : ∀ i, Integrable
      (fun D => (B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D)) G.μ :=
    fun i => ((integrable_const _).add (hP i)).sub (hC i)
  have e1 : ∫ D, ∑ i, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D)) ∂G.μ
      = ∑ i, ∫ D, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D)) ∂G.μ :=
    integral_finsetSum _ (fun i _ => hsup i)
  have e2 : ∫ D, (G.V D (p.s D) - ∑ i, (G.C i (p.s D) + G.E i p.t)) ∂G.μ
      = ∫ D, ((G.V D (p.s D) - ∑ i, ((B i).P (p.s D) + (B i).R p.t)) +
          ∑ i, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D))) ∂G.μ := by
    congr 1
    funext D
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have e3 : ∫ D, ((G.V D (p.s D) - ∑ i, ((B i).P (p.s D) + (B i).R p.t)) +
          ∑ i, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D))) ∂G.μ
      = ∫ D, (G.V D (p.s D) - ∑ i, ((B i).P (p.s D) + (B i).R p.t)) ∂G.μ +
        ∫ D, ∑ i, ((B i).R p.t - G.E i p.t + (B i).P (p.s D) - G.C i (p.s D)) ∂G.μ :=
    integral_add hbuy (integrable_finsetSum _ (fun i _ => hsup i))
  unfold scProfit buyerProfit supplierProfit
  rw [e2, e3, e1]
