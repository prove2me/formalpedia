-- Prove2me | solution 2 for BitcoinBlockV2.genesis_checkBlock
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:18:22.632045+00:00
-- url     : https://prove2.me/submissions/db7bc2d3-0fc1-4160-a4ff-21a6aad0eef2

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBlockV2

/-- **Genesis initialization.** The mainnet genesis block passes `CheckBlock`: its proof of work,
merkle root, structure, coinbase and sigop count are all as the source requires. -/
theorem solution : BitcoinBlockV2.checkBlock BitcoinSer.genesisBlock = true := by
  decide +kernel
