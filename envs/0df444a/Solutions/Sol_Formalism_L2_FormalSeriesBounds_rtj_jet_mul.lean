-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_jet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:42:01.325717+00:00
-- url     : https://prove2.me/submissions/8bfb7260-1818-4aa3-925a-b6eb4794d6cb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_subset
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_split_unique
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_antidiag_split
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_supp_of_supported
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_mfact_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (A : Set σ) (P Q : MvPolynomial σ K) (F G : MvPowerSeries σ K)
    (hP : P ∈ MvPolynomial.supported K A) (hQ : Q ∈ MvPolynomial.supported K Aᶜ)
    (hF : rtjSerIn A F) (hG : rtjSerIn Aᶜ G) :
    jetAt0 (P * Q) (F * G) = jetAt0 P F * jetAt0 Q G := by
  have hPs : ∀ a ∈ P.support, (↑a.support : Set σ) ⊆ A := fun a ha =>
    rtj_supp_of_supported hP a (MvPolynomial.mem_support_iff.mp ha)
  have hQs : ∀ b ∈ Q.support, (↑b.support : Set σ) ⊆ Aᶜ := fun b hb =>
    rtj_supp_of_supported hQ b (MvPolynomial.mem_support_iff.mp hb)
  have hterm : ∀ x ∈ P.support ×ˢ Q.support,
      MvPolynomial.coeff (x.1 + x.2) (P * Q) * (mfact (x.1 + x.2) : K) *
          MvPowerSeries.coeff (x.1 + x.2) (F * G) =
        (MvPolynomial.coeff x.1 P * (mfact x.1 : K) * MvPowerSeries.coeff x.1 F) *
          (MvPolynomial.coeff x.2 Q * (mfact x.2 : K) * MvPowerSeries.coeff x.2 G) := by
    intro x hx
    rw [Finset.mem_product] at hx
    have ha := hPs x.1 hx.1
    have hb := hQs x.2 hx.2
    have hdis : Disjoint x.1.support x.2.support := by
      rw [Finset.disjoint_left]
      intro i hia hib
      exact hb hib (ha hia)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul,
      rtj_antidiag_split (A := A) (fun c => MvPolynomial.coeff c P) (fun d => MvPolynomial.coeff d Q)
        (fun c hc => rtj_supp_of_supported hP c hc) (fun d hd => rtj_supp_of_supported hQ d hd) ha hb,
      rtj_antidiag_split (A := A) (fun c => MvPowerSeries.coeff c F) (fun d => MvPowerSeries.coeff d G)
        hF hG ha hb,
      rtj_mfact_add hdis]
    push_cast
    ring
  have hsupp : (P * Q).support ⊆ (P.support ×ˢ Q.support).image (fun x => x.1 + x.2) := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hm
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_product.mpr
      ⟨MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne),
        MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩, hx⟩
  have hinj : Set.InjOn (fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => x.1 + x.2) ↑(P.support ×ˢ Q.support) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_product.mp hx
    have hy' := Finset.mem_product.mp hy
    obtain ⟨h1, h2⟩ := rtj_split_unique (hPs _ hx'.1) (hQs _ hx'.2) (hPs _ hy'.1) (hQs _ hy'.2) hxy.symm
    exact Prod.ext h1.symm h2.symm
  rw [rtj_jet_subset (P * Q) (F * G) _ hsupp, Finset.sum_image hinj, Finset.sum_congr rfl hterm,
    rtj_jet_subset P F P.support subset_rfl, rtj_jet_subset Q G Q.support subset_rfl,
    Finset.sum_mul_sum, Finset.sum_product]
end Formalism.L2.FormalSeriesBounds
