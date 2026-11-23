-- Prove2me | solution 1 for DedekindZeta.sum_class_tsum_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:19.635371+00:00
-- url     : https://prove2.me/submissions/fa649a8c-42ff-4adf-a8e3-3dd1ff018b37

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_summable_absNorm_neg_cpow

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K),
        ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s)
      = ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  set F : NonzeroIdeal K → ℂ :=
    fun 𝔞 => (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) with hF
  -- `idealClass` partitions the nonzero integral ideals into the finitely many
  -- ideal classes; identify `NonzeroIdeal K` with the sigma of the fibres.
  set e := Equiv.sigmaFiberEquiv (idealClass K) with he
  have hsummable := summable_absNorm_neg_cpow K hs
  have hsig : Summable
      (fun p : (Σ c, {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c}) => F (e p)) :=
    (Equiv.summable_iff e).mpr hsummable
  -- Expand the full ideal sum as the (finite) class sum of fibrewise sums.
  rw [← Equiv.tsum_eq e F, hsig.tsum_sigma, tsum_fintype]
  refine Finset.sum_congr rfl (fun c _ => tsum_congr (fun 𝔟 => ?_))
  rw [he, hF]
  rfl
end DedekindZeta
