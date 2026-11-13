-- Prove2me | solution 1 for DirKECC1549.Main.scc_disjoint_paths
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T09:34:32.044202+00:00
-- url     : https://prove2.me/submissions/fcd3396d-18e2-456a-8eea-bdd495a5de47

import Theorems.Thm_DirKECC1549_Main_walks_in_scc
import Theorems.Thm_DirKECC1549_Main_induced_disjoint_paths
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n)
    (a x y : Fin n) (k : ℕ) (hx : StronglyConn G a x) (hy : StronglyConn G a y) :
    HasDisjointPaths G k x y ↔
      liftRel (sccOf G a) (HasDisjointPaths (induced G (sccOf G a)) k) x y := by
  have hx' : x ∈ sccOf G a := by simpa [sccOf] using hx
  have hy' : y ∈ sccOf G a := by simpa [sccOf] using hy
  exact induced_disjoint_paths G (sccOf G a) x y k hx' hy' (walks_in_scc G a x y hx hy)
