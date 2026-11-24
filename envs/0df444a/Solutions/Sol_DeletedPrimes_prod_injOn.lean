-- Prove2me | solution 1 for DeletedPrimes.prod_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:40.708283+00:00
-- url     : https://prove2.me/submissions/21d4751e-1c9b-4c42-a004-593060158507

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (T : Fin k → Finset ℕ) (hp : ∀ i, ∀ q ∈ T i, q.Prime)
    (hdisj : Pairwise fun i i' => Disjoint (T i) (T i')) :
    Set.InjOn (fun f : Fin k → ℕ => ∏ i, f i) (Fintype.piFinset T : Set (Fin k → ℕ)) := by
  intro f hf f' hf' heq
  simp only [Finset.mem_coe, Fintype.mem_piFinset] at hf hf'
  simp only at heq
  funext i
  have hpi : (f i).Prime := hp i _ (hf i)
  have hdvd : f i ∣ ∏ i, f' i := heq ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  obtain ⟨i', -, hi'⟩ := (Prime.dvd_finsetProd_iff hpi.prime f').mp hdvd
  have heq' : f i = f' i' := (Nat.prime_dvd_prime_iff_eq hpi (hp i' _ (hf' i'))).mp hi'
  have hii' : i = i' := by
    by_contra hne
    have hd := hdisj hne
    have h1 : f i ∈ T i := hf i
    have h2 : f i ∈ T i' := heq' ▸ hf' i'
    exact Finset.disjoint_left.mp hd h1 h2
  subst hii'
  exact heq'
end DeletedPrimes
